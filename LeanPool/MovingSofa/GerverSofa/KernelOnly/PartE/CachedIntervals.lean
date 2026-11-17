/-
Copyright (c) 2026 Dawid Trela and OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela, OpenAI
-/
module

public meta import Lean.Elab.Tactic.ElabTerm
public meta import Lean.Meta.Tactic.AuxLemma
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle005

/-!
# Shared exact interval evaluations for the Gerver certificates

The Part E leaves reuse the same first-angle intervals. Their sine and cosine evaluations
are certified here once, then supplied to the residual calculation by equality substitution.
The table records exact results of the existing depth-ten interval evaluator.
-/

@[expose] public section

namespace GerverSofa.PartE.CachedIntervals

open LeanCert.Core LeanCert.Engine GerverSofa.PartALeanCert

/-- The two residual intervals with the first-angle trigonometric values supplied explicitly. -/
def residualIntervals (phi theta : IntervalRat) (configuration : EvalConfig)
    (cosinePhi sinePhi : IntervalRat) : IntervalRat × IntervalRat :=
  let subtract := fun a b => IntervalRat.add a (IntervalRat.neg b)
  let scale := fun q a => IntervalRat.mul (IntervalRat.singleton q) a
  let one := IntervalRat.singleton 1
  let half := IntervalRat.singleton (1 / 2)
  let delta := subtract theta phi
  let cosineTheta := IntervalRat.cosComputable theta configuration.taylorDepth
  let sineTheta := IntervalRat.sinComputable theta configuration.taylorDepth
  let base := IntervalRat.add
    (IntervalRat.add (subtract (subtract (scale (1 / 2) kernelPiInterval) phi) theta)
      (scale (1 / 2) delta)) (scale (1 / 4) (IntervalRat.mul delta delta))
  let denominator := subtract cosinePhi
    (IntervalRat.mul (IntervalRat.add one (scale (1 / 2) delta)) sinePhi)
  let numerator := IntervalRat.add
    (IntervalRat.add (IntervalRat.add sinePhi half) (IntervalRat.neg (scale (1 / 2) cosinePhi)))
    (IntervalRat.mul base sinePhi)
  let numeratorB := IntervalRat.add
    (IntervalRat.mul numerator (IntervalRat.add one (scale (1 / 2) delta)))
    (IntervalRat.mul base denominator)
  let first := IntervalRat.add
    (IntervalRat.add (IntervalRat.add (IntervalRat.add
      (subtract (IntervalRat.mul numerator (subtract cosineTheta cosinePhi))
        (IntervalRat.mul (scale 2 numeratorB) sinePhi))
      (IntervalRat.mul (IntervalRat.mul (subtract delta one) cosineTheta) denominator))
      (IntervalRat.neg (IntervalRat.mul sineTheta denominator)))
      (IntervalRat.mul cosinePhi denominator)) (IntervalRat.mul sinePhi denominator)
  let second := IntervalRat.add
    (IntervalRat.add (IntervalRat.add (IntervalRat.add
      (subtract (IntervalRat.mul numerator (IntervalRat.add (scale 3 sineTheta) sinePhi))
        (IntervalRat.mul (scale 2 numeratorB) cosinePhi))
      (IntervalRat.mul (IntervalRat.mul (scale 3 (subtract delta one)) sineTheta) denominator))
      (IntervalRat.mul (scale 3 cosineTheta) denominator))
      (IntervalRat.neg (IntervalRat.mul sinePhi denominator)))
    (IntervalRat.mul cosinePhi denominator)
  (first, second)

/-- Rejection using previously evaluated first-angle sine and cosine intervals. -/
def rejected (cell : AngleCell) (configuration : EvalConfig)
    (cosinePhi sinePhi : IntervalRat) : Bool :=
  let residuals := residualIntervals cell.phiI cell.thetaI configuration cosinePhi sinePhi
  intervalExcludesZero residuals.1 || intervalExcludesZero residuals.2

/-- Substituting the original trigonometric evaluations recovers the original rejection test. -/
theorem rejected_eq (cell : AngleCell) (configuration : EvalConfig) :
    rejected cell configuration
      (IntervalRat.cosComputable cell.phiI configuration.taylorDepth)
      (IntervalRat.sinComputable cell.phiI configuration.taylorDepth) =
      cell.rejected configuration := by
  rfl

/-- Exact cached evaluations can be substituted into a closed rejection certificate. -/
theorem rejected_of_cached (cell : AngleCell) (configuration : EvalConfig)
    (cosinePhi sinePhi : IntervalRat)
    (cosineEquality :
      IntervalRat.cosComputable cell.phiI configuration.taylorDepth = cosinePhi)
    (sineEquality :
      IntervalRat.sinComputable cell.phiI configuration.taylorDepth = sinePhi)
    (certificate : rejected cell configuration cosinePhi sinePhi = true) :
    cell.rejected configuration = true := by
  rw [← cosineEquality, ← sineEquality, rejected_eq] at certificate
  exact certificate

open Lean Meta Elab Tactic in
/-- Check a closed interval equality directly in the kernel and retain its auxiliary lemma. -/
elab (name := gerverIntervalEq) "gerver_interval_eq" : tactic =>
  closeMainGoalUsing `gerver_interval_eq fun expectedType _ => do
    let expectedType ← instantiateMVars expectedType
    unless expectedType.isAppOfArity ``Eq 3 do throwError "expected an equality"
    let arguments := expectedType.getAppArgs
    let reflexivity := mkApp2 (mkConst ``Eq.refl [1]) arguments[0]! arguments[2]!
    let name ← mkAuxLemma [] expectedType reflexivity
    pure (mkConst name)

/-- The common first-angle interval in cache entry 0. -/
def input0 : IntervalRat :=
  ⟨(391 /
    20000 : ℚ),
   (6647 /
    320000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input0` at Taylor depth ten. -/
def cosine0 : IntervalRat :=
  ⟨(47928134464828891738487614336713221596037726568772792455585780050099 /
    47938476161552697262080000000000000000000000000000000000000000000000 : ℚ),
   (143787946164679857561702156635541592184726597248596551981267389449703 /
    143815428484658091786240000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input0` at Taylor depth ten. -/
def sine0 : IntervalRat :=
  ⟨(104125534967714590863183806932694681242594384344364809612564290011 /
    5326497351283633029120000000000000000000000000000000000000000000000 : ℚ),
   (142244086399024194011897184432443740461854920999518573935845912843 /
    6848353737364671037440000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine0_eq :
    IntervalRat.cosComputable input0 10 = cosine0 := by gerver_interval_eq

theorem sine0_eq :
    IntervalRat.sinComputable input0 10 = sine0 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 1. -/
def input1 : IntervalRat :=
  ⟨(6647 /
    320000 : ℚ),
   (3519 /
    160000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input1` at Taylor depth ten. -/
def cosine1 : IntervalRat :=
  ⟨(866733254807046963860659243608872913839928472271961009731627201 /
    866942928268820480000000000000000000000000000000000000000000000 : ℚ),
   (123822272218924031053505559571396809155063409196254000219930757 /
    123848989752688640000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input1` at Taylor depth ten. -/
def sine1 : IntervalRat :=
  ⟨(18006578346940827181095574229999288339403948065183225516537201 /
    866942928268820480000000000000000000000000000000000000000000000 : ℚ),
   (19065954896068035978329477867514259156918247813534654483462799 /
    866942928268820480000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine1_eq :
    IntervalRat.cosComputable input1 10 = cosine1 := by gerver_interval_eq

theorem sine1_eq :
    IntervalRat.sinComputable input1 10 = sine1 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 2. -/
def input2 : IntervalRat :=
  ⟨(3519 /
    160000 : ℚ),
   (7429 /
    320000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input2` at Taylor depth ten. -/
def cosine2 : IntervalRat :=
  ⟨(143776674288128724141539544906739931935080925638960615381783602612771 /
    143815428484658091786240000000000000000000000000000000000000000000000 : ℚ),
   (143780646485013046261656114305701467592981061136727401133368602187229 /
    143815428484658091786240000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input2` at Taylor depth ten. -/
def sine2 : IntervalRat :=
  ⟨(3162756458949930439528848612841653271148445570436196346473783732771 /
    143815428484658091786240000000000000000000000000000000000000000000000 : ℚ),
   (3338495890124900273555611647398209978071702637081111958934216267229 /
    143815428484658091786240000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine2_eq :
    IntervalRat.cosComputable input2 10 = cosine2 := by gerver_interval_eq

theorem sine2_eq :
    IntervalRat.sinComputable input2 10 = sine2 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 3. -/
def input3 : IntervalRat :=
  ⟨(7429 /
    320000 : ℚ),
   (391 /
    16000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input3` at Taylor depth ten. -/
def cosine3 : IntervalRat :=
  ⟨(2340047001047335151363224807800761107490548745499746053 /
    2340745906325815296000000000000000000000000000000000000 : ℚ),
   (2808138176847234444483946152484439041090513055288052434909 /
    2808895087590978355200000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input3` at Taylor depth ten. -/
def sine3 : IntervalRat :=
  ⟨(1811215685891949842832445877352598178634801175377601 /
    78024863544193843200000000000000000000000000000000000 : ℚ),
   (5719683992624890119994551592569478544320237346053597 /
    234074590632581529600000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine3_eq :
    IntervalRat.cosComputable input3 10 = cosine3 := by gerver_interval_eq

theorem sine3_eq :
    IntervalRat.sinComputable input3 10 = sine3 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 4. -/
def input4 : IntervalRat :=
  ⟨(391 /
    16000 : ℚ),
   (8211 /
    320000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input4` at Taylor depth ten. -/
def cosine4 : IntervalRat :=
  ⟨(253559235534709299227315014197978439903921180883638366951329123667 /
    253642731013506334720000000000000000000000000000000000000000000000 : ℚ),
   (253566998539252754125571492978670060281898885943266501247070876333 /
    253642731013506334720000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input4` at Taylor depth ten. -/
def sine4 : IntervalRat :=
  ⟨(6197714085348813733654551723114514593229386406389091712929123667 /
    253642731013506334720000000000000000000000000000000000000000000000 : ℚ),
   (6507666187564448718008252067534469980141690352835228287070876333 /
    253642731013506334720000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine4_eq :
    IntervalRat.cosComputable input4 10 = cosine4 := by gerver_interval_eq

theorem sine4_eq :
    IntervalRat.sinComputable input4 10 = sine4 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 5. -/
def input5 : IntervalRat :=
  ⟨(8211 /
    320000 : ℚ),
   (4301 /
    160000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input5` at Taylor depth ten. -/
def cosine5 : IntervalRat :=
  ⟨(6381546107334651103779150241196755784008348278889513750819226609 /
    6383852471797678080000000000000000000000000000000000000000000000 : ℚ),
   (6381751022858549152905818952382772997114057695162300013513460891 /
    6383852471797678080000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input5` at Taylor depth ten. -/
def sine5 : IntervalRat :=
  ⟨(163785937462040911935028213007638513069876689570521443211636609 /
    6383852471797678080000000000000000000000000000000000000000000000 : ℚ),
   (171587103945850401659151539227613635589488572122639620788363391 /
    6383852471797678080000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine5_eq :
    IntervalRat.cosComputable input5 10 = cosine5 := by gerver_interval_eq

theorem sine5_eq :
    IntervalRat.sinComputable input5 10 = sine5 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 6. -/
def input6 : IntervalRat :=
  ⟨(4301 /
    160000 : ℚ),
   (8993 /
    320000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input6` at Taylor depth ten. -/
def cosine6 : IntervalRat :=
  ⟨(47919546741547955696975357109312293647946044822737059203557994998581 /
    47938476161552697262080000000000000000000000000000000000000000000000 : ℚ),
   (20537638753558963301644780750324591602025785959061004261317086577751 /
    20545061212094013112320000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input6` at Taylor depth ten. -/
def sine6 : IntervalRat :=
  ⟨(429492180913888140522233579117971042934894061387498379191012519527 /
    15979492053850899087360000000000000000000000000000000000000000000000 : ℚ),
   (449019581203590496065712171235328369798939554888031430728987480473 /
    15979492053850899087360000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine6_eq :
    IntervalRat.cosComputable input6 10 = cosine6 := by gerver_interval_eq

theorem sine6_eq :
    IntervalRat.sinComputable input6 10 = sine6 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 7. -/
def input7 : IntervalRat :=
  ⟨(8993 /
    320000 : ℚ),
   (1173 /
    40000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input7` at Taylor depth ten. -/
def cosine7 : IntervalRat :=
  ⟨(13222811684845610250641901459337074425422266281521584201437 /
    13228499271680000000000000000000000000000000000000000000000 : ℚ),
   (846289651627445790721300009273360453234358563268209642761157 /
    846623953387520000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input7` at Taylor depth ten. -/
def sine7 : IntervalRat :=
  ⟨(23231805471072616158248841679917308665696751220208772707 /
    826781204480000000000000000000000000000000000000000000000 : ℚ),
   (865791697115967400928716563549390576965771456872217381 /
    29527900160000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine7_eq :
    IntervalRat.cosComputable input7 10 = cosine7 := by gerver_interval_eq

theorem sine7_eq :
    IntervalRat.sinComputable input7 10 = sine7 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 8. -/
def input8 : IntervalRat :=
  ⟨(391 /
    20000 : ℚ),
   (3519 /
    160000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input8` at Taylor depth ten. -/
def cosine8 : IntervalRat :=
  ⟨(866733253946175463567935183671918382901721273555005293225977201 /
    866942928268820480000000000000000000000000000000000000000000000 : ℚ),
   (866777261069848128514481373774700001085785563710268557858822799 /
    866942928268820480000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input8` at Taylor depth ten. -/
def sine8 : IntervalRat :=
  ⟨(2421052550368326408889591304555631479161391238629396788076743 /
    123848989752688640000000000000000000000000000000000000000000000 : ℚ),
   (2723730208767985859448031822175306081167840640481259211923257 /
    123848989752688640000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine8_eq :
    IntervalRat.cosComputable input8 10 = cosine8 := by gerver_interval_eq

theorem sine8_eq :
    IntervalRat.sinComputable input8 10 = sine8 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 9. -/
def input9 : IntervalRat :=
  ⟨(3519 /
    160000 : ℚ),
   (391 /
    16000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input9` at Taylor depth ten. -/
def cosine9 : IntervalRat :=
  ⟨(501438642392131882195744573681413273462871762788378211 /
    501588408498388992000000000000000000000000000000000000 : ℚ),
   (87756742342398946742824151444333177423982326509080070373 /
    87777971487218073600000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input9` at Taylor depth ten. -/
def sine9 : IntervalRat :=
  ⟨(2206142413788167590285497155605879786572244038131087 /
    100317681699677798400000000000000000000000000000000000 : ℚ),
   (17159209965607215363762126231757823977451715698240791 /
    702223771897744588800000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine9_eq :
    IntervalRat.cosComputable input9 10 = cosine9 := by gerver_interval_eq

theorem sine9_eq :
    IntervalRat.sinComputable input9 10 = sine9 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 10. -/
def input10 : IntervalRat :=
  ⟨(1173 /
    40000 : ℚ),
   (391 /
    12800 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input10` at Taylor depth ten. -/
def cosine10 : IntervalRat :=
  ⟨(942069090698199119769297028219834111279009163183277209393 /
    942508792117055270330302464000000000000000000000000000000 : ℚ),
   (84116389800002028193313477030593796164038908539405587574249 /
    84152570724737077708062720000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input10` at Taylor depth ten. -/
def sine10 : IntervalRat :=
  ⟨(5526954424850932751463277259148795361195929472122748477 /
    188501758423411054066060492800000000000000000000000000000 : ℚ),
   (230292575983196334811398513544827646496956965405809723 /
    7540070336936442162642419712000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine10_eq :
    IntervalRat.cosComputable input10 10 = cosine10 := by gerver_interval_eq

theorem sine10_eq :
    IntervalRat.sinComputable input10 10 = sine10 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 11. -/
def input11 : IntervalRat :=
  ⟨(391 /
    12800 : ℚ),
   (5083 /
    160000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input11` at Taylor depth ten. -/
def cosine11 : IntervalRat :=
  ⟨(23395647952003845009241716468591898718863812841313937233043572911 /
    23407459063258152960000000000000000000000000000000000000000000000 : ℚ),
   (70189617288780270057023629637280420798868433813440499950283343767 /
    70222377189774458880000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input11` at Taylor depth ten. -/
def sine11 : IntervalRat :=
  ⟨(79433828683610079965615107778682077219701298295910054105535879 /
    2600828784806461440000000000000000000000000000000000000000000000 : ℚ),
   (743510073324939769833940884281443073649743583077434513050177089 /
    23407459063258152960000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine11_eq :
    IntervalRat.cosComputable input11 10 = cosine11 := by gerver_interval_eq

theorem sine11_eq :
    IntervalRat.sinComputable input11 10 = sine11 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 12. -/
def input12 : IntervalRat :=
  ⟨(5083 /
    160000 : ℚ),
   (10557 /
    320000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input12` at Taylor depth ten. -/
def cosine12 : IntervalRat :=
  ⟨(1774532988301923941857543933109488038689964045066379570814884665547 /
    1775499117094544343040000000000000000000000000000000000000000000000 : ℚ),
   (1774603234026101112377961625557140590633962965318314335386433734453 /
    1775499117094544343040000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input12` at Taylor depth ten. -/
def sine12 : IntervalRat :=
  ⟨(56395156330640250805025892591899375674144014458845134490015545547 /
    1775499117094544343040000000000000000000000000000000000000000000000 : ℚ),
   (58564973288342359005515186282180056677945573682531549541984454453 /
    1775499117094544343040000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine12_eq :
    IntervalRat.cosComputable input12 10 = cosine12 := by gerver_interval_eq

theorem sine12_eq :
    IntervalRat.sinComputable input12 10 = sine12 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 13. -/
def input13 : IntervalRat :=
  ⟨(10557 /
    320000 : ℚ),
   (2737 /
    80000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input13` at Taylor depth ten. -/
def cosine13 : IntervalRat :=
  ⟨(9790915658611287472046909091945662665748472417874783928515957 /
    9796648603484160000000000000000000000000000000000000000000000 : ℚ),
   (156661086059595030152195243699260830809481816891636999840801563 /
    156746377655746560000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input13` at Taylor depth ten. -/
def sine13 : IntervalRat :=
  ⟨(161567256784438166191405834800662885904841793153151875682041 /
    4898324301742080000000000000000000000000000000000000000000000 : ℚ),
   (167553522750536198786956473472669341109358408609770936817959 /
    4898324301742080000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine13_eq :
    IntervalRat.cosComputable input13 10 = cosine13 := by gerver_interval_eq

theorem sine13_eq :
    IntervalRat.sinComputable input13 10 = sine13 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 14. -/
def input14 : IntervalRat :=
  ⟨(2737 /
    80000 : ℚ),
   (11339 /
    320000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input14` at Taylor depth ten. -/
def cosine14 : IntervalRat :=
  ⟨(47908383443148414690332415644434979889243507500318411482088000651087 /
    47938476161552697262080000000000000000000000000000000000000000000000 : ℚ),
   (143731269659801101137655286996855531309753190728021151012086078046739 /
    143815428484658091786240000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input14` at Taylor depth ten. -/
def sine14 : IntervalRat :=
  ⟨(546583973303567897112872516513459176170666958200536946987937497029 /
    15979492053850899087360000000000000000000000000000000000000000000000 : ℚ),
   (1698338581217395607729099320734188805666747175584961819772187508913 /
    47938476161552697262080000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine14_eq :
    IntervalRat.cosComputable input14 10 = cosine14 := by gerver_interval_eq

theorem sine14_eq :
    IntervalRat.sinComputable input14 10 = sine14 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 15. -/
def input15 : IntervalRat :=
  ⟨(11339 /
    320000 : ℚ),
   (1173 /
    32000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input15` at Taylor depth ten. -/
def cosine15 : IntervalRat :=
  ⟨(88715319499208630634338509991907510495095801733984623711 /
    88774955854727217152000000000000000000000000000000000000 : ℚ),
   (316854390724037663566348709229971873561818755433236298843 /
    317053413766882918400000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input15` at Taylor depth ten. -/
def sine15 : IntervalRat :=
  ⟨(628996130910848759812165332202541030450230972841751683 /
    17754991170945443430400000000000000000000000000000000000 : ℚ),
   (650695207493101361452158347880542016832799599288449917 /
    17754991170945443430400000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine15_eq :
    IntervalRat.cosComputable input15 10 = cosine15 := by gerver_interval_eq

theorem sine15_eq :
    IntervalRat.sinComputable input15 10 = sine15 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 16. -/
def input16 : IntervalRat :=
  ⟨(3 /
    20 : ℚ),
   (1 /
    5 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input16` at Taylor depth ten. -/
def cosine16 : IntervalRat :=
  ⟨(488999486062019039 /
    498960000000000000 : ℚ),
   (7893846351628344001 /
    7983360000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input16` at Taylor depth ten. -/
def sine16 : IntervalRat :=
  ⟨(148691201591133613 /
    997920000000000000 : ℚ),
   (49709264019636503 /
    249480000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine16_eq :
    IntervalRat.cosComputable input16 10 = cosine16 := by gerver_interval_eq

theorem sine16_eq :
    IntervalRat.sinComputable input16 10 = sine16 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 17. -/
def input17 : IntervalRat :=
  ⟨(1 /
    10 : ℚ),
   (3 /
    20 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input17` at Taylor depth ten. -/
def cosine17 : IntervalRat :=
  ⟨(14255853466642098019 /
    14417920000000000000 : ℚ),
   (100421758660734708107 /
    100925440000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input17` at Taylor depth ten. -/
def sine17 : IntervalRat :=
  ⟨(1436387981911972259 /
    14417920000000000000 : ℚ),
   (15113613018523714187 /
    100925440000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine17_eq :
    IntervalRat.cosComputable input17 10 = cosine17 := by gerver_interval_eq

theorem sine17_eq :
    IntervalRat.sinComputable input17 10 = sine17 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 18. -/
def input18 : IntervalRat :=
  ⟨(0 /
    1 : ℚ),
   (1 /
    80 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input18` at Taylor depth ten. -/
def cosine18 : IntervalRat :=
  ⟨(34285591341092044799999999999 /
    34288270112194560000000000000 : ℚ),
   (1 /
    1 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input18` at Taylor depth ten. -/
def sine18 : IntervalRat :=
  ⟨(-1 /
    34288270112194560000000000000 : ℚ),
   (428603376402432000000000001 /
    34288270112194560000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine18_eq :
    IntervalRat.cosComputable input18 10 = cosine18 := by gerver_interval_eq

theorem sine18_eq :
    IntervalRat.sinComputable input18 10 = sine18 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 19. -/
def input19 : IntervalRat :=
  ⟨(1 /
    80 : ℚ),
   (3 /
    160 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input19` at Taylor depth ten. -/
def cosine19 : IntervalRat :=
  ⟨(123827219705923194856500626339 /
    123848989752688640000000000000 : ℚ),
   (866875200336814034451824529547 /
    866942928268820480000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input19` at Taylor depth ten. -/
def sine19 : IntervalRat :=
  ⟨(1548021662907980151908644259 /
    123848989752688640000000000000 : ℚ),
   (16254756600504693398048770187 /
    866942928268820480000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine19_eq :
    IntervalRat.cosComputable input19 10 = cosine19 := by gerver_interval_eq

theorem sine19_eq :
    IntervalRat.sinComputable input19 10 = sine19 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 20. -/
def input20 : IntervalRat :=
  ⟨(3 /
    160 : ℚ),
   (1 /
    40 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input20` at Taylor depth ten. -/
def cosine20 : IntervalRat :=
  ⟨(535586802214006997633515513 /
    535754220503040000000000000 : ℚ),
   (8570560797782177671192280417 /
    8572067528048640000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input20` at Taylor depth ten. -/
def sine20 : IntervalRat :=
  ⟨(2511086314465866931534117 /
    133938555125760000000000000 : ℚ),
   (837066921304952289711377 /
    33484638781440000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine20_eq :
    IntervalRat.cosComputable input20 10 = cosine20 := by gerver_interval_eq

theorem sine20_eq :
    IntervalRat.sinComputable input20 10 = sine20 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 21. -/
def input21 : IntervalRat :=
  ⟨(3 /
    160 : ℚ),
   (7 /
    320 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input21` at Taylor depth ten. -/
def cosine21 : IntervalRat :=
  ⟨(20540145789699166339615698830295311 /
    20545061212094013112320000000000000 : ℚ),
   (20541449919561871571420741944847089 /
    20545061212094013112320000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input21` at Taylor depth ten. -/
def sine21 : IntervalRat :=
  ⟨(385189175976776321024970928276751 /
    20545061212094013112320000000000000 : ℚ),
   (449396881253152060925937389419249 /
    20545061212094013112320000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine21_eq :
    IntervalRat.cosComputable input21 10 = cosine21 := by gerver_interval_eq

theorem sine21_eq :
    IntervalRat.sinComputable input21 10 = sine21 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 22. -/
def input22 : IntervalRat :=
  ⟨(7 /
    320 : ℚ),
   (1 /
    40 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input22` at Taylor depth ten. -/
def cosine22 : IntervalRat :=
  ⟨(2856462954587795036354595811 /
    2857355842682880000000000000 : ℚ),
   (548481068847427756069364442073 /
    548612321795112960000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input22` at Taylor depth ten. -/
def sine22 : IntervalRat :=
  ⟨(31249074156239409262103123 /
    1428677921341440000000000000 : ℚ),
   (1488087483455527662766823 /
    59528246722560000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine22_eq :
    IntervalRat.cosComputable input22 10 = cosine22 := by gerver_interval_eq

theorem sine22_eq :
    IntervalRat.sinComputable input22 10 = sine22 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 23. -/
def input23 : IntervalRat :=
  ⟨(1 /
    40 : ℚ),
   (9 /
    320 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input23` at Taylor depth ten. -/
def cosine23 : IntervalRat :=
  ⟨(1774796929895837037957983152926391 /
    1775499117094544343040000000000000 : ℚ),
   (253563472884835019068351497891887 /
    253642731013506334720000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input23` at Taylor depth ten. -/
def sine23 : IntervalRat :=
  ⟨(44381626245465123865086269091511 /
    1775499117094544343040000000000000 : ℚ),
   (49930711216441005979233282396489 /
    1775499117094544343040000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine23_eq :
    IntervalRat.cosComputable input23 10 = cosine23 := by gerver_interval_eq

theorem sine23_eq :
    IntervalRat.sinComputable input23 10 = sine23 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 24. -/
def input24 : IntervalRat :=
  ⟨(9 /
    320 : ℚ),
   (1 /
    32 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input24` at Taylor depth ten. -/
def cosine24 : IntervalRat :=
  ⟨(898407567101463148296845753 /
    898846428029113073664000000 : ℚ),
   (44924547808727746950264137399 /
    44942321401455653683200000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input24` at Taylor depth ten. -/
def sine24 : IntervalRat :=
  ⟨(25275941358636902530043471 /
    898846428029113073664000000 : ℚ),
   (802435654958608872870107 /
    25681326515117516390400000 : ℚ),
   by decide +kernel⟩

theorem cosine24_eq :
    IntervalRat.cosComputable input24 10 = cosine24 := by gerver_interval_eq

theorem sine24_eq :
    IntervalRat.sinComputable input24 10 = sine24 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 25. -/
def input25 : IntervalRat :=
  ⟨(1 /
    32 : ℚ),
   (11 /
    320 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input25` at Taylor depth ten. -/
def cosine25 : IntervalRat :=
  ⟨(4355468676448098436416866489125133 /
    4358043287413881569280000000000000 : ℚ),
   (1866820948338238573851245716774943 /
    1867732837463092101120000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input25` at Taylor depth ten. -/
def sine25 : IntervalRat :=
  ⟨(136162032994425065519539087525133 /
    4358043287413881569280000000000000 : ℚ),
   (149783356675544693891937392474867 /
    4358043287413881569280000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine25_eq :
    IntervalRat.cosComputable input25 10 = cosine25 := by gerver_interval_eq

theorem sine25_eq :
    IntervalRat.sinComputable input25 10 = sine25 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 26. -/
def input26 : IntervalRat :=
  ⟨(11 /
    320 : ℚ),
   (3 /
    80 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input26` at Taylor depth ten. -/
def cosine26 : IntervalRat :=
  ⟨(6768229836280338518987597713 /
    6772991627100160000000000000 : ℚ),
   (108303847599871537003725204017 /
    108367866033602560000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input26` at Taylor depth ten. -/
def sine26 : IntervalRat :=
  ⟨(29095877855740828995840751 /
    846623953387520000000000000 : ℚ),
   (15871073079395984082390437 /
    423311976693760000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine26_eq :
    IntervalRat.cosComputable input26 10 = cosine26 := by gerver_interval_eq

theorem sine26_eq :
    IntervalRat.sinComputable input26 10 = sine26 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 27. -/
def input27 : IntervalRat :=
  ⟨(3 /
    80 : ℚ),
   (7 /
    160 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input27` at Taylor depth ten. -/
def cosine27 : IntervalRat :=
  ⟨(10022168579348447527736490550031 /
    10031768169967779840000000000000 : ℚ),
   (10024715708004397797654170301169 /
    10031768169967779840000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input27` at Taylor depth ten. -/
def sine27 : IntervalRat :=
  ⟨(376071305866143493324837012751 /
    10031768169967779840000000000000 : ℚ),
   (438787002469907980413173611249 /
    10031768169967779840000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine27_eq :
    IntervalRat.cosComputable input27 10 = cosine27 := by gerver_interval_eq

theorem sine27_eq :
    IntervalRat.sinComputable input27 10 = sine27 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 28. -/
def input28 : IntervalRat :=
  ⟨(7 /
    160 : ℚ),
   (1 /
    20 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input28` at Taylor depth ten. -/
def cosine28 : IntervalRat :=
  ⟨(8360697414656180881846921 /
    8371159695360000000000000 : ℚ),
   (178413864594789964840104947 /
    178584740167680000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input28` at Taylor depth ten. -/
def sine28 : IntervalRat :=
  ⟨(122028550670025761302867 /
    2790386565120000000000000 : ℚ),
   (17434353212527667900501 /
    348798320640000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine28_eq :
    IntervalRat.cosComputable input28 10 = cosine28 := by gerver_interval_eq

theorem sine28_eq :
    IntervalRat.sinComputable input28 10 = sine28 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 29. -/
def input29 : IntervalRat :=
  ⟨(3 /
    80 : ℚ),
   (13 /
    320 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input29` at Taylor depth ten. -/
def cosine29 : IntervalRat :=
  ⟨(143696766573764665854387048630113483 /
    143815428484658091786240000000000000 : ℚ),
   (143714322168175287548244017349749557 /
    143815428484658091786240000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input29` at Taylor depth ten. -/
def sine29 : IntervalRat :=
  ⟨(5391595224757363554593793756533963 /
    143815428484658091786240000000000000 : ℚ),
   (5841132558827245236829106877066037 /
    143815428484658091786240000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine29_eq :
    IntervalRat.cosComputable input29 10 = cosine29 := by gerver_interval_eq

theorem sine29_eq :
    IntervalRat.sinComputable input29 10 = sine29 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 30. -/
def input30 : IntervalRat :=
  ⟨(13 /
    320 : ℚ),
   (7 /
    160 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input30` at Taylor depth ten. -/
def cosine30 : IntervalRat :=
  ⟨(3340722924887681831005815974927 /
    3343922723322593280000000000000 : ℚ),
   (20046982644472242057499661438713 /
    20063536339935559680000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input30` at Taylor depth ten. -/
def sine30 : IntervalRat :=
  ⟨(135803527647316273574763678917 /
    3343922723322593280000000000000 : ℚ),
   (146256381901626200852956937083 /
    3343922723322593280000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine30_eq :
    IntervalRat.cosComputable input30 10 = cosine30 := by gerver_interval_eq

theorem sine30_eq :
    IntervalRat.sinComputable input30 10 = sine30 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 31. -/
def input31 : IntervalRat :=
  ⟨(11 /
    320 : ℚ),
   (23 /
    640 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input31` at Taylor depth ten. -/
def cosine31 : IntervalRat :=
  ⟨(294343820360203149721571733139832214713 /
    294533997536579771978219520000000000000 : ℚ),
   (98119999865325419980240238859512071789 /
    98177999178859923992739840000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input31` at Taylor depth ten. -/
def sine31 : IntervalRat :=
  ⟨(1124714107334052648778010542290350897 /
    32725999726286641330913280000000000000 : ℚ),
   (1175859010711614181650221446056529103 /
    32725999726286641330913280000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine31_eq :
    IntervalRat.cosComputable input31 10 = cosine31 := by gerver_interval_eq

theorem sine31_eq :
    IntervalRat.sinComputable input31 10 = sine31 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 32. -/
def input32 : IntervalRat :=
  ⟨(23 /
    640 : ℚ),
   (3 /
    80 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input32` at Taylor depth ten. -/
def cosine32 : IntervalRat :=
  ⟨(108291678078049359185351798833 /
    108367866033602560000000000000 : ℚ),
   (6931065310255258569635086177913 /
    6935543426150563840000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input32` at Taylor depth ten. -/
def sine32 : IntervalRat :=
  ⟨(973389369518236093893031657 /
    27091966508400640000000000000 : ℚ),
   (126966259476519858095161621 /
    3386495813550080000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine32_eq :
    IntervalRat.cosComputable input32 10 = cosine32 := by gerver_interval_eq

theorem sine32_eq :
    IntervalRat.sinComputable input32 10 = sine32 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 33. -/
def input33 : IntervalRat :=
  ⟨(9 /
    320 : ℚ),
   (19 /
    640 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input33` at Taylor depth ten. -/
def cosine33 : IntervalRat :=
  ⟨(294404212667839900367138993438151715541 /
    294533997536579771978219520000000000000 : ℚ),
   (294417515595000493089476749914451574059 /
    294533997536579771978219520000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input33` at Taylor depth ten. -/
def sine33 : IntervalRat :=
  ⟨(8282551915489270494190268064577069781 /
    294533997536579771978219520000000000000 : ℚ),
   (8742825332121888765561070002457042219 /
    294533997536579771978219520000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine33_eq :
    IntervalRat.cosComputable input33 10 = cosine33 := by gerver_interval_eq

theorem sine33_eq :
    IntervalRat.sinComputable input33 10 = sine33 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 34. -/
def input34 : IntervalRat :=
  ⟨(19 /
    640 : ℚ),
   (1 /
    32 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input34` at Taylor depth ten. -/
def cosine34 : IntervalRat :=
  ⟨(7187260563241386387693962429 /
    7190771424232904589312000000 : ℚ),
   (35494335295461753054027328189 /
    35509982341890886860800000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input34` at Taylor depth ten. -/
def sine34 : IntervalRat :=
  ⟨(2964462260291286754417417 /
    99871825336568119296000000 : ℚ),
   (1872321670368975458489543 /
    59923095201940871577600000 : ℚ),
   by decide +kernel⟩

theorem cosine34_eq :
    IntervalRat.cosComputable input34 10 = cosine34 := by gerver_interval_eq

theorem sine34_eq :
    IntervalRat.sinComputable input34 10 = sine34 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 35. -/
def input35 : IntervalRat :=
  ⟨(1 /
    32 : ℚ),
   (21 /
    640 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input35` at Taylor depth ten. -/
def cosine35 : IntervalRat :=
  ⟨(519180694761153736526462369183430437 /
    519460313115660973506560000000000000 : ℚ),
   (519206693141158552511607688493369563 /
    519460313115660973506560000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input35` at Taylor depth ten. -/
def sine35 : IntervalRat :=
  ⟨(16230221998854600298711651026630437 /
    519460313115660973506560000000000000 : ℚ),
   (17042017456078158416074468653369563 /
    519460313115660973506560000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine35_eq :
    IntervalRat.cosComputable input35 10 = cosine35 := by gerver_interval_eq

theorem sine35_eq :
    IntervalRat.sinComputable input35 10 = sine35 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 36. -/
def input36 : IntervalRat :=
  ⟨(21 /
    640 : ℚ),
   (11 /
    320 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input36` at Taylor depth ten. -/
def cosine36 : IntervalRat :=
  ⟨(13066406093775131751712333058198579 /
    13074129862241644707840000000000000 : ℚ),
   (3266773089479568807927459776814199 /
    3268532465560411176960000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input36` at Taylor depth ten. -/
def sine36 : IntervalRat :=
  ⟨(428910404355271078837101471887399 /
    13074129862241644707840000000000000 : ℚ),
   (449342572767860674534340096208601 /
    13074129862241644707840000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine36_eq :
    IntervalRat.cosComputable input36 10 = cosine36 := by gerver_interval_eq

theorem sine36_eq :
    IntervalRat.sinComputable input36 10 = sine36 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 37. -/
def input37 : IntervalRat :=
  ⟨(1 /
    20 : ℚ),
   (1 /
    16 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input37` at Taylor depth ten. -/
def cosine37 : IntervalRat :=
  ⟨(146010943081591162782853 /
    146296619145363456000000 : ℚ),
   (10958535592103859977534729 /
    10972246435902259200000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input37` at Taylor depth ten. -/
def sine37 : IntervalRat :=
  ⟨(812229921417496926109 /
    16255179905040384000000 : ℚ),
   (609315308856917782997 /
    9753107943024230400000 : ℚ),
   by decide +kernel⟩

theorem cosine37_eq :
    IntervalRat.cosComputable input37 10 = cosine37 := by gerver_interval_eq

theorem sine37_eq :
    IntervalRat.sinComputable input37 10 = sine37 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 38. -/
def input38 : IntervalRat :=
  ⟨(1 /
    16 : ℚ),
   (3 /
    40 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input38` at Taylor depth ten. -/
def cosine38 : IntervalRat :=
  ⟨(412228319570641749686251 /
    413390602240000000000000 : ℚ),
   (1650334308564499799158121 /
    1653562408960000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input38` at Taylor depth ten. -/
def sine38 : IntervalRat :=
  ⟨(12906347632323217185313 /
    206695301120000000000000 : ℚ),
   (15492057878264020627187 /
    206695301120000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine38_eq :
    IntervalRat.cosComputable input38 10 = cosine38 := by gerver_interval_eq

theorem sine38_eq :
    IntervalRat.sinComputable input38 10 = sine38 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 39. -/
def input39 : IntervalRat :=
  ⟨(3 /
    40 : ℚ),
   (1 /
    10 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input39` at Taylor depth ten. -/
def cosine39 : IntervalRat :=
  ⟨(508381561904872090417 /
    510935040000000000000 : ℚ),
   (1164569674238875640279 /
    1167851520000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input39` at Taylor depth ten. -/
def sine39 : IntervalRat :=
  ⟨(38256279078283533997 /
    510935040000000000000 : ℚ),
   (12761406946718211407 /
    127733760000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine39_eq :
    IntervalRat.cosComputable input39 10 = cosine39 := by gerver_interval_eq

theorem sine39_eq :
    IntervalRat.sinComputable input39 10 = sine39 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 40. -/
def input40 : IntervalRat :=
  ⟨(3 /
    80 : ℚ),
   (5 /
    128 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input40` at Taylor depth ten. -/
def cosine40 : IntervalRat :=
  ⟨(172212991860516330324856920833 /
    172344464844261535146112450560 : ℚ),
   (150695387981680110797327891067797 /
    150801406738728843252848394240000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input40` at Taylor depth ten. -/
def sine40 : IntervalRat :=
  ⟨(9045783519254455236583109275 /
    241282250781966149204557430784 : ℚ),
   (235571977117927271511655780061 /
    6032056269549153730113935769600 : ℚ),
   by decide +kernel⟩

theorem cosine40_eq :
    IntervalRat.cosComputable input40 10 = cosine40 := by gerver_interval_eq

theorem sine40_eq :
    IntervalRat.sinComputable input40 10 = sine40 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 41. -/
def input41 : IntervalRat :=
  ⟨(5 /
    128 : ℚ),
   (13 /
    320 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input41` at Taylor depth ten. -/
def cosine41 : IntervalRat :=
  ⟨(143696767756787770669938283941168463 /
    143815428484658091786240000000000000 : ℚ),
   (23950953518323683001988380439818277 /
    23969238080776348631040000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input41` at Taylor depth ten. -/
def sine41 : IntervalRat :=
  ⟨(208009075371534579388705382948369 /
    5326497351283633029120000000000000 : ℚ),
   (1947005359918723731085389053464679 /
    47938476161552697262080000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine41_eq :
    IntervalRat.cosComputable input41 10 = cosine41 := by gerver_interval_eq

theorem sine41_eq :
    IntervalRat.sinComputable input41 10 = sine41 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 42. -/
def input42 : IntervalRat :=
  ⟨(7 /
    160 : ℚ),
   (29 /
    640 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input42` at Taylor depth ten. -/
def cosine42 : IntervalRat :=
  ⟨(294231673824789027338305122122314719131 /
    294533997536579771978219520000000000000 : ℚ),
   (32694685280396868199192626481089084541 /
    32725999726286641330913280000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input42` at Taylor depth ten. -/
def sine42 : IntervalRat :=
  ⟨(1431272580383130962992025775221638019 /
    32725999726286641330913280000000000000 : ℚ),
   (4447271554841904783327132997582189943 /
    98177999178859923992739840000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine42_eq :
    IntervalRat.cosComputable input42 10 = cosine42 := by gerver_interval_eq

theorem sine42_eq :
    IntervalRat.sinComputable input42 10 = sine42 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 43. -/
def input43 : IntervalRat :=
  ⟨(29 /
    640 : ℚ),
   (3 /
    64 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input43` at Taylor depth ten. -/
def cosine43 : IntervalRat :=
  ⟨(22701425014227610479607998809 /
    22726388698810167590912000000 : ℚ),
   (35473534066401084439043562709 /
    35509982341890886860800000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input43` at Taylor depth ten. -/
def sine43 : IntervalRat :=
  ⟨(1029412406454597649623782309 /
    22726388698810167590912000000 : ℚ),
   (212986992160807219498978783 /
    4545277739762033518182400000 : ℚ),
   by decide +kernel⟩

theorem cosine43_eq :
    IntervalRat.cosComputable input43 10 = cosine43 := by gerver_interval_eq

theorem sine43_eq :
    IntervalRat.sinComputable input43 10 = sine43 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 44. -/
def input44 : IntervalRat :=
  ⟨(3 /
    64 : ℚ),
   (1 /
    20 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input44` at Taylor depth ten. -/
def cosine44 : IntervalRat :=
  ⟨(133771162585400625034699241 /
    133938555125760000000000000 : ℚ),
   (4892943962993268305739672847 /
    4898324301742080000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input44` at Taylor depth ten. -/
def sine44 : IntervalRat :=
  ⟨(12551508142998106644107857 /
    267877110251520000000000000 : ℚ),
   (836809446830123319611423 /
    16742319390720000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine44_eq :
    IntervalRat.cosComputable input44 10 = cosine44 := by gerver_interval_eq

theorem sine44_eq :
    IntervalRat.sinComputable input44 10 = sine44 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 45. -/
def input45 : IntervalRat :=
  ⟨(1 /
    80 : ℚ),
   (1 /
    40 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input45` at Taylor depth ten. -/
def cosine45 : IntervalRat :=
  ⟨(11158058322689101826639981 /
    11161546260480000000000000 : ℚ),
   (133928091721135337503679953 /
    133938555125760000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input45` at Taylor depth ten. -/
def sine45 : IntervalRat :=
  ⟨(7750266394787746133537 /
    620085903360000000000000 : ℚ),
   (139515695053700697603667 /
    5580773130240000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine45_eq :
    IntervalRat.cosComputable input45 10 = cosine45 := by gerver_interval_eq

theorem sine45_eq :
    IntervalRat.sinComputable input45 10 = sine45 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 46. -/
def input46 : IntervalRat :=
  ⟨(1 /
    40 : ℚ),
   (1 /
    32 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input46` at Taylor depth ten. -/
def cosine46 : IntervalRat :=
  ⟨(898407561029779629979639183 /
    898846428029113073664000000 : ℚ),
   (2496015448274234721173345537 /
    2496795633414202982400000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input46` at Taylor depth ten. -/
def sine46 : IntervalRat :=
  ⟨(7489167799846922991522949 /
    299615476009704357888000000 : ℚ),
   (1872401672426169495803263 /
    59923095201940871577600000 : ℚ),
   by decide +kernel⟩

theorem cosine46_eq :
    IntervalRat.cosComputable input46 10 = cosine46 := by gerver_interval_eq

theorem sine46_eq :
    IntervalRat.sinComputable input46 10 = sine46 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 47. -/
def input47 : IntervalRat :=
  ⟨(1 /
    32 : ℚ),
   (3 /
    80 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input47` at Taylor depth ten. -/
def cosine47 : IntervalRat :=
  ⟨(211507179840558704299844219 /
    211655988346880000000000000 : ℚ),
   (1692421222455828559199149373 /
    1693247906775040000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input47` at Taylor depth ten. -/
def sine47 : IntervalRat :=
  ⟨(13225398993546291268747813 /
    423311976693760000000000000 : ℚ),
   (15871615616413568082502187 /
    423311976693760000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine47_eq :
    IntervalRat.cosComputable input47 10 = cosine47 := by gerver_interval_eq

theorem sine47_eq :
    IntervalRat.sinComputable input47 10 = sine47 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 48. -/
def input48 : IntervalRat :=
  ⟨(13 /
    320 : ℚ),
   (27 /
    640 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input48` at Taylor depth ten. -/
def cosine48 : IntervalRat :=
  ⟨(3632986789676636043478438191564917357 /
    3636222191809626814545920000000000000 : ℚ),
   (3633222043311570570826365239704919443 /
    3636222191809626814545920000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input48` at Taylor depth ten. -/
def sine48 : IntervalRat :=
  ⟨(147677711394650259591611009567851117 /
    3636222191809626814545920000000000000 : ℚ),
   (153360931625593419503814820066196883 /
    3636222191809626814545920000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine48_eq :
    IntervalRat.cosComputable input48 10 = cosine48 := by gerver_interval_eq

theorem sine48_eq :
    IntervalRat.sinComputable input48 10 = sine48 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 49. -/
def input49 : IntervalRat :=
  ⟨(27 /
    640 : ℚ),
   (7 /
    160 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input49` at Taylor depth ten. -/
def cosine49 : IntervalRat :=
  ⟨(80177351025438259669380707469223 /
    80254145359742238720000000000000 : ℚ),
   (1282923826915538610990901923066887 /
    1284066325755875819520000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input49` at Taylor depth ten. -/
def sine49 : IntervalRat :=
  ⟨(423080221620846780162368852501 /
    10031768169967779840000000000000 : ℚ),
   (438759681619404976342013926249 /
    10031768169967779840000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine49_eq :
    IntervalRat.cosComputable input49 10 = cosine49 := by gerver_interval_eq

theorem sine49_eq :
    IntervalRat.sinComputable input49 10 = sine49 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 50. -/
def input50 : IntervalRat :=
  ⟨(1 /
    20 : ℚ),
   (9 /
    160 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input50` at Taylor depth ten. -/
def cosine50 : IntervalRat :=
  ⟨(865571683169782136301969632951 /
    866942928268820480000000000000 : ℚ),
   (865859535320258769326943211849 /
    866942928268820480000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input50` at Taylor depth ten. -/
def sine50 : IntervalRat :=
  ⟨(6189184346262878960653701073 /
    123848989752688640000000000000 : ℚ),
   (6963603422081977450588794927 /
    123848989752688640000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine50_eq :
    IntervalRat.cosComputable input50 10 = cosine50 := by gerver_interval_eq

theorem sine50_eq :
    IntervalRat.sinComputable input50 10 = sine50 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 51. -/
def input51 : IntervalRat :=
  ⟨(9 /
    160 : ℚ),
   (1 /
    16 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input51` at Taylor depth ten. -/
def cosine51 : IntervalRat :=
  ⟨(15644031309827467255823 /
    15674637765574656000000 : ℚ),
   (43819574596379368041576649 /
    43888985743609036800000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input51` at Taylor depth ten. -/
def sine51 : IntervalRat :=
  ⟨(3524497770952609989257 /
    62698551062298624000000 : ℚ),
   (5483230710171126742493 /
    87777971487218073600000 : ℚ),
   by decide +kernel⟩

theorem cosine51_eq :
    IntervalRat.cosComputable input51 10 = cosine51 := by gerver_interval_eq

theorem sine51_eq :
    IntervalRat.sinComputable input51 10 = sine51 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 52. -/
def input52 : IntervalRat :=
  ⟨(13 /
    320 : ℚ),
   (53 /
    1280 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input52` at Taylor depth ten. -/
def cosine52 : IntervalRat :=
  ⟨(7440600084176608048479779737463608807843 /
    7446983048826115716190044160000000000000 : ℚ),
   (602707935612045512018677416623657812224877 /
    603205626954915373011393576960000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input52` at Taylor depth ten. -/
def sine52 : IntervalRat :=
  ⟨(8166075631836176005951491998256747338801 /
    201068542318305124337131192320000000000000 : ℚ),
   (8323204473706604773460553393876741301199 /
    201068542318305124337131192320000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine52_eq :
    IntervalRat.cosComputable input52 10 = cosine52 := by gerver_interval_eq

theorem sine52_eq :
    IntervalRat.sinComputable input52 10 = sine52 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 53. -/
def input53 : IntervalRat :=
  ⟨(53 /
    1280 : ℚ),
   (27 /
    640 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input53` at Taylor depth ten. -/
def cosine53 : IntervalRat :=
  ⟨(3632986806956899008956153304193235957 /
    3636222191809626814545920000000000000 : ℚ),
   (3633105543461361130958447286397514293 /
    3636222191809626814545920000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input53` at Taylor depth ten. -/
def sine53 : IntervalRat :=
  ⟨(150517667526113521659780002416619117 /
    3636222191809626814545920000000000000 : ℚ),
   (153359293249258178603743691926676883 /
    3636222191809626814545920000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine53_eq :
    IntervalRat.cosComputable input53 10 = cosine53 := by gerver_interval_eq

theorem sine53_eq :
    IntervalRat.sinComputable input53 10 = sine53 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 54. -/
def input54 : IntervalRat :=
  ⟨(157 /
    4000 : ℚ),
   (8067 /
    128000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input54` at Taylor depth ten. -/
def cosine54 : IntervalRat :=
  ⟨(74321954114167539085997728385304942122016647530684484838490357 /
    74469830488261157161900441600000000000000000000000000000000000 : ℚ),
   (74412486760007351849659299302892279840904857451646211169189643 /
    74469830488261157161900441600000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input54` at Taylor depth ten. -/
def sine54 : IntervalRat :=
  ⟨(417286575917743656246161688707425990113254989847124119126051 /
    10638547212608736737414348800000000000000000000000000000000000 : ℚ),
   (670305697369179162789054039295040787817380761263613800873949 /
    10638547212608736737414348800000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine54_eq :
    IntervalRat.cosComputable input54 10 = cosine54 := by gerver_interval_eq

theorem sine54_eq :
    IntervalRat.sinComputable input54 10 = sine54 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 55. -/
def input55 : IntervalRat :=
  ⟨(8067 /
    128000 : ℚ),
   (1111 /
    12800 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input55` at Taylor depth ten. -/
def cosine55 : IntervalRat :=
  ⟨(136575953292155124618750256852847278978708383758324083 /
    137092187944298948411680358400000000000000000000000000 : ℚ),
   (3420502423502449277176734244860857712308612971780841693 /
    3427304698607473710292008960000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input55` at Taylor depth ten. -/
def sine55 : IntervalRat :=
  ⟨(49309568811722369190035484642523990547008160132701 /
    783383931110279705209602048000000000000000000000000 : ℚ),
   (475651972256808871549635243299651879271561968532341 /
    5483687517771957936467214336000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine55_eq :
    IntervalRat.cosComputable input55 10 = cosine55 := by gerver_interval_eq

theorem sine55_eq :
    IntervalRat.sinComputable input55 10 = sine55 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 56. -/
def input56 : IntervalRat :=
  ⟨(1111 /
    12800 : ℚ),
   (4299 /
    32000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input56` at Taylor depth ten. -/
def cosine56 : IntervalRat :=
  ⟨(17594868500849950779456132625960620411709796818960471021 /
    17754991170945443430400000000000000000000000000000000000 : ℚ),
   (17688211368734294358094896821740766085474061664114841479 /
    17754991170945443430400000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input56` at Taylor depth ten. -/
def sine56 : IntervalRat :=
  ⟨(1536443870384287502277490010754063650699312341424221021 /
    17754991170945443430400000000000000000000000000000000000 : ℚ),
   (2382279810941986806993180920536166682299760258575778979 /
    17754991170945443430400000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine56_eq :
    IntervalRat.cosComputable input56 10 = cosine56 := by gerver_interval_eq

theorem sine56_eq :
    IntervalRat.sinComputable input56 10 = sine56 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 57. -/
def input57 : IntervalRat :=
  ⟨(4299 /
    32000 : ℚ),
   (11641 /
    64000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input57` at Taylor depth ten. -/
def cosine57 : IntervalRat :=
  ⟨(413813009428693166695501636688829477719025330149230922337137 /
    420762853623685388540313600000000000000000000000000000000000 : ℚ),
   (416976300615085724613800989304944959011942507483372515742863 /
    420762853623685388540313600000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input57` at Taylor depth ten. -/
def sine57 : IntervalRat :=
  ⟨(56215449685636631454726103769068845246546597182666358369137 /
    420762853623685388540313600000000000000000000000000000000000 : ℚ),
   (76302985261333809063127930535116306925907001192122761630863 /
    420762853623685388540313600000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine57_eq :
    IntervalRat.cosComputable input57 10 = cosine57 := by gerver_interval_eq

theorem sine57_eq :
    IntervalRat.sinComputable input57 10 = sine57 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 58. -/
def input58 : IntervalRat :=
  ⟨(11641 /
    64000 : ℚ),
   (3671 /
    16000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input58` at Taylor depth ten. -/
def cosine58 : IntervalRat :=
  ⟨(1367583122061886219612820377437676607518016907237438883 /
    1404447543795489177600000000000000000000000000000000000 : ℚ),
   (7367023127924067062795037086892731231081335546145101499 /
    7490386900242608947200000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input58` at Taylor depth ten. -/
def sine58 : IntervalRat :=
  ⟨(14067682136638822183509753034443765247878060754841681 /
    78024863544193843200000000000000000000000000000000000 : ℚ),
   (17803377957036976620291656888107824151400299682658319 /
    78024863544193843200000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine58_eq :
    IntervalRat.cosComputable input58 10 = cosine58 := by gerver_interval_eq

theorem sine58_eq :
    IntervalRat.sinComputable input58 10 = sine58 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 59. -/
def input59 : IntervalRat :=
  ⟨(157 /
    4000 : ℚ),
   (13091 /
    256000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input59` at Taylor depth ten. -/
def cosine59 : IntervalRat :=
  ⟨(12337501136817204349877262427577077944527086579506020979678747129509 /
    12353651240036666839273340456140800000000000000000000000000000000000 : ℚ),
   (4114712509210250692965851552424598819525479079968012607960348503497 /
    4117883746678888946424446818713600000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input59` at Taylor depth ten. -/
def sine59 : IntervalRat :=
  ⟨(161556501045686275311028201636145213306235731522077387861821608503 /
    4117883746678888946424446818713600000000000000000000000000000000000 : ℚ),
   (30074428961021079214730174280471049920094841661887149851236913071 /
    588269106668412706632063831244800000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine59_eq :
    IntervalRat.cosComputable input59 10 = cosine59 := by gerver_interval_eq

theorem sine59_eq :
    IntervalRat.sinComputable input59 10 = sine59 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 60. -/
def input60 : IntervalRat :=
  ⟨(13091 /
    256000 : ℚ),
   (8067 /
    128000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input60` at Taylor depth ten. -/
def cosine60 : IntervalRat :=
  ⟨(10617423907713924315151080377930999999021651216601095954350051 /
    10638547212608736737414348800000000000000000000000000000000000 : ℚ),
   (74372494750797414439279658049301215160302407216413083249535643 /
    74469830488261157161900441600000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input60` at Taylor depth ten. -/
def sine60 : IntervalRat :=
  ⟨(3805622145502414567674668352006523563879367427117301793882357 /
    74469830488261157161900441600000000000000000000000000000000000 : ℚ),
   (4691299625704613304724158026409578058293839668135050206117643 /
    74469830488261157161900441600000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine60_eq :
    IntervalRat.cosComputable input60 10 = cosine60 := by gerver_interval_eq

theorem sine60_eq :
    IntervalRat.sinComputable input60 10 = sine60 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 61. -/
def input61 : IntervalRat :=
  ⟨(3671 /
    16000 : ℚ),
   (2077 /
    6400 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input61` at Taylor depth ten. -/
def cosine61 : IntervalRat :=
  ⟨(232576300395738493306735833135402415656820734242657 /
    245444997947149809981849600000000000000000000000000 : ℚ),
   (17928097071626621391271831920256460681117113515290261 /
    18408374846036235748638720000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input61` at Taylor depth ten. -/
def sine61 : IntervalRat :=
  ⟨(2213134943478245819770098260546790215300028695177 /
    9817799917885992399273984000000000000000000000000 : ℚ),
   (1052791875685272592076377592260905753945213719677 /
    3272599972628664133091328000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine61_eq :
    IntervalRat.cosComputable input61 10 = cosine61 := by gerver_interval_eq

theorem sine61_eq :
    IntervalRat.sinComputable input61 10 = sine61 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 62. -/
def input62 : IntervalRat :=
  ⟨(2077 /
    6400 : ℚ),
   (3357 /
    8000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input62` at Taylor depth ten. -/
def cosine62 : IntervalRat :=
  ⟨(15454707571876452606965425872170633756090342205013 /
    16932479067750400000000000000000000000000000000000 : ℚ),
   (256861576966373761739469276443265664793266263860417 /
    270919665084006400000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input62` at Taylor depth ten. -/
def sine62 : IntervalRat :=
  ⟨(1333674040643374833054286990628282584918182797347 /
    4233119766937600000000000000000000000000000000000 : ℚ),
   (1745416171801323855839369512180874144622051577653 /
    4233119766937600000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine62_eq :
    IntervalRat.cosComputable input62 10 = cosine62 := by gerver_interval_eq

theorem sine62_eq :
    IntervalRat.sinComputable input62 10 = sine62 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 63. -/
def input63 : IntervalRat :=
  ⟨(157 /
    4000 : ℚ),
   (23139 /
    512000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input63` at Taylor depth ten. -/
def cosine63 : IntervalRat :=
  ⟨(312030171729747986687648640928767983193551502195229373557530016912981 /
    312349107896235724528787669804646400000000000000000000000000000000000 : ℚ),
   (312108552183214573274134791858358050432481937075653756335274738543019 /
    312349107896235724528787669804646400000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input63` at Taylor depth ten. -/
def sine63 : IntervalRat :=
  ⟨(12255529522463057165253216327292697525944886434178905841755602064981 /
    312349107896235724528787669804646400000000000000000000000000000000000 : ℚ),
   (14112481396612733338535188728221172701605721201527206692362797935019 /
    312349107896235724528787669804646400000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine63_eq :
    IntervalRat.cosComputable input63 10 = cosine63 := by gerver_interval_eq

theorem sine63_eq :
    IntervalRat.sinComputable input63 10 = sine63 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 64. -/
def input64 : IntervalRat :=
  ⟨(23139 /
    512000 : ℚ),
   (13091 /
    256000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input64` at Taylor depth ten. -/
def cosine64 : IntervalRat :=
  ⟨(12337501812292467006745367724343376532020152144606534634527424969509 /
    12353651240036666839273340456140800000000000000000000000000000000000 : ℚ),
   (12341038194941978854188701630015595639022221026146346203386963450491 /
    12353651240036666839273340456140800000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input64` at Taylor depth ten. -/
def sine64 : IntervalRat :=
  ⟨(558059701223405815406823782580455515633514779485305194405304825509 /
    12353651240036666839273340456140800000000000000000000000000000000000 : ℚ),
   (631510173674942399843913108086621727175561907434166092501575174491 /
    12353651240036666839273340456140800000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine64_eq :
    IntervalRat.cosComputable input64 10 = cosine64 := by gerver_interval_eq

theorem sine64_eq :
    IntervalRat.sinComputable input64 10 = sine64 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 65. -/
def input65 : IntervalRat :=
  ⟨(1111 /
    12800 : ℚ),
   (14153 /
    128000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input65` at Taylor depth ten. -/
def cosine65 : IntervalRat :=
  ⟨(666134007867221276044231308596920850020791080414489908685973167 /
    670228474394350414457103974400000000000000000000000000000000000 : ℚ),
   (6009357569470397942602807437107054240885146877528994240706241497 /
    6032056269549153730113935769600000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input65` at Taylor depth ten. -/
def sine65 : IntervalRat :=
  ⟨(174165735191021265535875194935777796517281456788227477097919501 /
    2010685423183051243371311923200000000000000000000000000000000000 : ℚ),
   (222043134930812945581170044688043777671153173050210922902080499 /
    2010685423183051243371311923200000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine65_eq :
    IntervalRat.cosComputable input65 10 = cosine65 := by gerver_interval_eq

theorem sine65_eq :
    IntervalRat.sinComputable input65 10 = sine65 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 66. -/
def input66 : IntervalRat :=
  ⟨(14153 /
    128000 : ℚ),
   (4299 /
    32000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input66` at Taylor depth ten. -/
def cosine66 : IntervalRat :=
  ⟨(8797465555866298238981476655245864947863811634131147323 /
    8877495585472721715200000000000000000000000000000000000 : ℚ),
   (282345918561733547123394380155794333219306640172039776289 /
    284079858735127094886400000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input66` at Taylor depth ten. -/
def sine66 : IntervalRat :=
  ⟨(1957273220781967691267709486023985412614432898254221021 /
    17754991170945443430400000000000000000000000000000000000 : ℚ),
   (2380416172298581806035915922981817689239710550135778979 /
    17754991170945443430400000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine66_eq :
    IntervalRat.cosComputable input66 10 = cosine66 := by gerver_interval_eq

theorem sine66_eq :
    IntervalRat.sinComputable input66 10 = sine66 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 67. -/
def input67 : IntervalRat :=
  ⟨(8067 /
    128000 : ℚ),
   (19177 /
    256000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input67` at Taylor depth ten. -/
def cosine67 : IntervalRat :=
  ⟨(12319001259102688311465825031544159272949589828198796048782569581127 /
    12353651240036666839273340456140800000000000000000000000000000000000 : ℚ),
   (12329128646107461881697082582106125837175165108641345684991827858873 /
    12353651240036666839273340456140800000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input67` at Taylor depth ten. -/
def sine67 : IntervalRat :=
  ⟨(777841550138989695388029478212021796556751012829692860403572845127 /
    12353651240036666839273340456140800000000000000000000000000000000000 : ℚ),
   (924801499632561480925502437107822833876525997643491597774987154873 /
    12353651240036666839273340456140800000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine67_eq :
    IntervalRat.cosComputable input67 10 = cosine67 := by gerver_interval_eq

theorem sine67_eq :
    IntervalRat.sinComputable input67 10 = sine67 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 68. -/
def input68 : IntervalRat :=
  ⟨(19177 /
    256000 : ℚ),
   (1111 /
    12800 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input68` at Taylor depth ten. -/
def cosine68 : IntervalRat :=
  ⟨(136576023831695683878531435425239555739391842537765873 /
    137092187944298948411680358400000000000000000000000000 : ℚ),
   (3037950684854652532916843455454420669989109216579670239 /
    3046493065428865520259563520000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input68` at Taylor depth ten. -/
def sine68 : IntervalRat :=
  ⟨(136756082182527659582930485283079294275812962622681 /
    1827895839257319312155738112000000000000000000000000 : ℚ),
   (52835773010886402816845178218504089146812998023949 /
    609298613085773104051912704000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine68_eq :
    IntervalRat.cosComputable input68 10 = cosine68 := by gerver_interval_eq

theorem sine68_eq :
    IntervalRat.sinComputable input68 10 = sine68 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 69. -/
def input69 : IntervalRat :=
  ⟨(13091 /
    256000 : ℚ),
   (1169 /
    20480 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input69` at Taylor depth ten. -/
def cosine69 : IntervalRat :=
  ⟨(39413773038357502270012788486058861425682438672029764452759 /
    39478071474812001425243069690326233907200000000000000000000 : ℚ),
   (73924628662903141850558275268216917236022971967578148330789643 /
    74021384015272502672330755669361688576000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input69` at Taylor depth ten. -/
def sine69 : IntervalRat :=
  ⟨(672560979524392409044872865852909733349434550087290050013 /
    13159357158270667141747689896775411302400000000000000000000 : ℚ),
   (90097178628091611418671816009000833312941777175262984913 /
    1579122858992480057009722787613049356288000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine69_eq :
    IntervalRat.cosComputable input69 10 = cosine69 := by gerver_interval_eq

theorem sine69_eq :
    IntervalRat.sinComputable input69 10 = sine69 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 70. -/
def input70 : IntervalRat :=
  ⟨(1169 /
    20480 : ℚ),
   (8067 /
    128000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input70` at Taylor depth ten. -/
def cosine70 : IntervalRat :=
  ⟨(74321975279785749439603937617898038045414400453453325837944857 /
    74469830488261157161900441600000000000000000000000000000000000 : ℚ),
   (297394216986840775909777584064086760965908668474367557048611197 /
    297879321953044628647601766400000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input70` at Taylor depth ten. -/
def sine70 : IntervalRat :=
  ⟨(4247930241057566207523075677690850363437325273501532673882357 /
    74469830488261157161900441600000000000000000000000000000000000 : ℚ),
   (4690796621492013124314525882294050768957408582935967326117643 /
    74469830488261157161900441600000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine70_eq :
    IntervalRat.cosComputable input70 10 = cosine70 := by gerver_interval_eq

theorem sine70_eq :
    IntervalRat.sinComputable input70 10 = sine70 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 71. -/
def input71 : IntervalRat :=
  ⟨(3357 /
    8000 : ℚ),
   (16471 /
    32000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input71` at Taylor depth ten. -/
def cosine71 : IntervalRat :=
  ⟨(178630881989326939557081550257143631274865171886036546047 /
    205450612120940131123200000000000000000000000000000000000 : ℚ),
   (187759233991380784488554530578269275031750501066181053953 /
    205450612120940131123200000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input71` at Taylor depth ten. -/
def sine71 : IntervalRat :=
  ⟨(82438740316787110641864619528724607008447861753673282047 /
    205450612120940131123200000000000000000000000000000000000 : ℚ),
   (102686742075771732272379947568576600071119857383606717953 /
    205450612120940131123200000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine71_eq :
    IntervalRat.cosComputable input71 10 = cosine71 := by gerver_interval_eq

theorem sine71_eq :
    IntervalRat.sinComputable input71 10 = sine71 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 72. -/
def input72 : IntervalRat :=
  ⟨(16471 /
    32000 : ℚ),
   (9757 /
    16000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input72` at Taylor depth ten. -/
def cosine72 : IntervalRat :=
  ⟨(17409165519698243056652125045394797239949572787173379 /
    21279508239325593600000000000000000000000000000000000 : ℚ),
   (55641745561365029560284098993866269951470937221430613 /
    63838524717976780800000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input72` at Taylor depth ten. -/
def sine72 : IntervalRat :=
  ⟨(10283026434832347317341164571177733209458630658296379 /
    21279508239325593600000000000000000000000000000000000 : ℚ),
   (12414107714331118874337968004866717077647256941703621 /
    21279508239325593600000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine72_eq :
    IntervalRat.cosComputable input72 10 = cosine72 := by gerver_interval_eq

theorem sine72_eq :
    IntervalRat.sinComputable input72 10 = sine72 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 73. -/
def input73 : IntervalRat :=
  ⟨(9757 /
    16000 : ℚ),
   (22557 /
    32000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input73` at Taylor depth ten. -/
def cosine73 : IntervalRat :=
  ⟨(13478276895229217534876235630368450998187917669061589547 /
    17754991170945443430400000000000000000000000000000000000 : ℚ),
   (14588724746531370965290226361694854672523167180451370453 /
    17754991170945443430400000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input73` at Taylor depth ten. -/
def sine73 : IntervalRat :=
  ⟨(9947030494198162947674084856590379783810263387240917547 /
    17754991170945443430400000000000000000000000000000000000 : ℚ),
   (11759007786757314639046947610997451840744167240599082453 /
    17754991170945443430400000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine73_eq :
    IntervalRat.cosComputable input73 10 = cosine73 := by gerver_interval_eq

theorem sine73_eq :
    IntervalRat.sinComputable input73 10 = sine73 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 74. -/
def input74 : IntervalRat :=
  ⟨(22557 /
    32000 : ℚ),
   (4 /
    5 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input74` at Taylor depth ten. -/
def cosine74 : IntervalRat :=
  ⟨(885157002829563765599274287 /
    1277337600000000000000000000 : ℚ),
   (80006008127116756079803771263185261 /
    104639496192000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input74` at Taylor depth ten. -/
def sine74 : IntervalRat :=
  ⟨(206517833064747733343123350127 /
    326998425600000000000000000000 : ℚ),
   (2685484945191334606974221 /
    3649536000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine74_eq :
    IntervalRat.cosComputable input74 10 = cosine74 := by gerver_interval_eq

theorem sine74_eq :
    IntervalRat.sinComputable input74 10 = sine74 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 75. -/
def input75 : IntervalRat :=
  ⟨(1173 /
    32000 : ℚ),
   (12121 /
    320000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input75` at Taylor depth ten. -/
def cosine75 : IntervalRat :=
  ⟨(143712270274128393355367857970900391403486751859300465133842304354679 /
    143815428484658091786240000000000000000000000000000000000000000000000 : ℚ),
   (143718819031184224285018543329589513674059705920824360702730495645321 /
    143815428484658091786240000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input75` at Taylor depth ten. -/
def sine75 : IntervalRat :=
  ⟨(5270473779547986569330093440184762675385826594097659617589504354679 /
    143815428484658091786240000000000000000000000000000000000000000000000 : ℚ),
   (778034131963635937827591824325903384560598059345673403201499377903 /
    20545061212094013112320000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine75_eq :
    IntervalRat.cosComputable input75 10 = cosine75 := by gerver_interval_eq

theorem sine75_eq :
    IntervalRat.sinComputable input75 10 = sine75 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 76. -/
def input76 : IntervalRat :=
  ⟨(12121 /
    320000 : ℚ),
   (391 /
    10000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input76` at Taylor depth ten. -/
def cosine76 : IntervalRat :=
  ⟨(87132932334068246130425615985793751363571302352978653383 /
    87199580160000000000000000000000000000000000000000000000 : ℚ),
   (38240709439371865361659308154630416867575838133260075701507 /
    38268158607360000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input76` at Taylor depth ten. -/
def sine76 : IntervalRat :=
  ⟨(1100705019591397398856533487930227425053997155005280711 /
    29066526720000000000000000000000000000000000000000000000 : ℚ),
   (11835723429492199285382750232433560647598998730963059 /
    302776320000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine76_eq :
    IntervalRat.cosComputable input76 10 = cosine76 := by gerver_interval_eq

theorem sine76_eq :
    IntervalRat.sinComputable input76 10 = sine76 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 77. -/
def input77 : IntervalRat :=
  ⟨(3 /
    80 : ℚ),
   (49 /
    1280 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input77` at Taylor depth ten. -/
def cosine77 : IntervalRat :=
  ⟨(86109099095351223226542931284489770196953 /
    86172232422130767573056225280000000000000 : ℚ),
   (86111649970165919123664800895114098679847 /
    86172232422130767573056225280000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input77` at Taylor depth ten. -/
def sine77 : IntervalRat :=
  ⟨(3230669512251222173985930960469637291993 /
    86172232422130767573056225280000000000000 : ℚ),
   (3298007677315182853245650733664159572007 /
    86172232422130767573056225280000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine77_eq :
    IntervalRat.cosComputable input77 10 = cosine77 := by gerver_interval_eq

theorem sine77_eq :
    IntervalRat.sinComputable input77 10 = sine77 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 78. -/
def input78 : IntervalRat :=
  ⟨(7 /
    160 : ℚ),
   (3 /
    64 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input78` at Taylor depth ten. -/
def cosine78 : IntervalRat :=
  ⟨(22701424724703423856615430309 /
    22726388698810167590912000000 : ℚ),
   (567616070422268827830035266531 /
    568159717470254189772800000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input78` at Taylor depth ten. -/
def sine78 : IntervalRat :=
  ⟨(993915424388290844838274213 /
    22726388698810167590912000000 : ℚ),
   (212991933192652021758831583 /
    4545277739762033518182400000 : ℚ),
   by decide +kernel⟩

theorem cosine78_eq :
    IntervalRat.cosComputable input78 10 = cosine78 := by gerver_interval_eq

theorem sine78_eq :
    IntervalRat.sinComputable input78 10 = sine78 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 79. -/
def input79 : IntervalRat :=
  ⟨(5 /
    128 : ℚ),
   (401 /
    10240 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input79` at Taylor depth ten. -/
def cosine79 : IntervalRat :=
  ⟨(5177524427285008069753371566162594656988917431195599 /
    5181496881069075187063152896855318200320000000000000 : ℚ),
   (575282690870491471667086161174204215367482063200489 /
    575721875674341687451461432983924244480000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input79` at Taylor depth ten. -/
def sine79 : IntervalRat :=
  ⟨(9635737839386639840530872322934103682279115771219 /
    246737946717575008907769185564538961920000000000000 : ℚ),
   (9659839485588352362039093500842103984920884228781 /
    246737946717575008907769185564538961920000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine79_eq :
    IntervalRat.cosComputable input79 10 = cosine79 := by gerver_interval_eq

theorem sine79_eq :
    IntervalRat.sinComputable input79 10 = sine79 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 80. -/
def input80 : IntervalRat :=
  ⟨(401 /
    10240 : ℚ),
   (803 /
    20480 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input80` at Taylor depth ten. -/
def cosine80 : IntervalRat :=
  ⟨(321319688829712576231593300911930006674483971074704901 /
    321566836740286847972889004023020959825920000000000000 : ℚ),
   (963960912259412182072706018303796361706860316441718257 /
    964700510220860543918667012069062879477760000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input80` at Taylor depth ten. -/
def sine80 : IntervalRat :=
  ⟨(12589381289716959486479911003926870505746585411995141 /
    321566836740286847972889004023020959825920000000000000 : ℚ),
   (12605086813819352371506196225263676697626751737444859 /
    321566836740286847972889004023020959825920000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine80_eq :
    IntervalRat.cosComputable input80 10 = cosine80 := by gerver_interval_eq

theorem sine80_eq :
    IntervalRat.sinComputable input80 10 = sine80 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 81. -/
def input81 : IntervalRat :=
  ⟨(803 /
    20480 : ℚ),
   (201 /
    5120 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input81` at Taylor depth ten. -/
def cosine81 : IntervalRat :=
  ⟨(31210844628052742593660424353691201195489127259 /
    31234910789623572452878766980464640000000000000 : ℚ),
   (124843617858247734887398291380913650538216333589 /
    124939643158494289811515067921858560000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input81` at Taylor depth ten. -/
def sine81 : IntervalRat :=
  ⟨(1224374576401286046151925974324123595863887479 /
    31234910789623572452878766980464640000000000000 : ℚ),
   (1225900109824579912260911026792282241775024521 /
    31234910789623572452878766980464640000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine81_eq :
    IntervalRat.cosComputable input81 10 = cosine81 := by gerver_interval_eq

theorem sine81_eq :
    IntervalRat.sinComputable input81 10 = sine81 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 82. -/
def input82 : IntervalRat :=
  ⟨(201 /
    5120 : ℚ),
   (161 /
    4096 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input82` at Taylor depth ten. -/
def cosine82 : IntervalRat :=
  ⟨(19389273707819040422650104586544180138680014293017 /
    19404261691299594940535473614189150490066944000000 : ℚ),
   (484732773167410919433702633143139463646826005132687 /
    485106542282489873513386840354728762251673600000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input82` at Taylor depth ten. -/
def sine82 : IntervalRat :=
  ⟨(761572725286554854926565996982336008495067777049 /
    19404261691299594940535473614189150490066944000000 : ℚ),
   (152504088538810307608862902907257118114859669499 /
    3880852338259918988107094722837830098013388800000 : ℚ),
   by decide +kernel⟩

theorem cosine82_eq :
    IntervalRat.cosComputable input82 10 = cosine82 := by gerver_interval_eq

theorem sine82_eq :
    IntervalRat.sinComputable input82 10 = sine82 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 83. -/
def input83 : IntervalRat :=
  ⟨(161 /
    4096 : ℚ),
   (403 /
    10240 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input83` at Taylor depth ten. -/
def cosine83 : IntervalRat :=
  ⟨(1725828236463848468380876730386799850832914419335751 /
    1727165627023025062354384298951772733440000000000000 : ℚ),
   (5177494660257685400194935893032379207280266602892747 /
    5181496881069075187063152896855318200320000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input83` at Taylor depth ten. -/
def sine83 : IntervalRat :=
  ⟨(67871554922072254059602319849616647829954656535751 /
    1727165627023025062354384298951772733440000000000000 : ℚ),
   (67955910926103114828010636129529310943334303464249 /
    1727165627023025062354384298951772733440000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine83_eq :
    IntervalRat.cosComputable input83 10 = cosine83 := by gerver_interval_eq

theorem sine83_eq :
    IntervalRat.sinComputable input83 10 = sine83 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 84. -/
def input84 : IntervalRat :=
  ⟨(403 /
    10240 : ℚ),
   (807 /
    20480 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input84` at Taylor depth ten. -/
def cosine84 : IntervalRat :=
  ⟨(130907015869426183821293036284496188937511085056958777 /
    131008711264561308433399223861230761410560000000000000 : ℚ),
   (18701038254140483566065637212674652441986852554439489 /
    18715530180651615490485603408747251630080000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input84` at Taylor depth ten. -/
def sine84 : IntervalRat :=
  ⟨(5154575083287692715506174491689492523081738966442297 /
    131008711264561308433399223861230761410560000000000000 : ℚ),
   (5160973646506438987568393023601237432164631489109703 /
    131008711264561308433399223861230761410560000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine84_eq :
    IntervalRat.cosComputable input84 10 = cosine84 := by gerver_interval_eq

theorem sine84_eq :
    IntervalRat.sinComputable input84 10 = sine84 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 85. -/
def input85 : IntervalRat :=
  ⟨(807 /
    20480 : ℚ),
   (101 /
    2560 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input85` at Taylor depth ten. -/
def cosine85 : IntervalRat :=
  ⟨(9875230361458374221186076790594864538534328137 /
    9882920992029333471418672364912640000000000000 : ℚ),
   (632015960854703540535213519648501159510585947017 /
    632506943489877342170795031354408960000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input85` at Taylor depth ten. -/
def sine85 : IntervalRat :=
  ⟨(48666066612946314334891845232009760229002899 /
    1235365124003666683927334045614080000000000000 : ℚ),
   (6960914686591748414742511344509784724932443 /
    176480732000523811989619149373440000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine85_eq :
    IntervalRat.cosComputable input85 10 = cosine85 := by gerver_interval_eq

theorem sine85_eq :
    IntervalRat.sinComputable input85 10 = sine85 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 86. -/
def input86 : IntervalRat :=
  ⟨(101 /
    2560 : ℚ),
   (81 /
    2048 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input86` at Taylor depth ten. -/
def cosine86 : IntervalRat :=
  ⟨(818164115188451480149113205225174794793797487 /
    818804445403508177708745149132692258816000000 : ℚ),
   (20454181845470661104447328616379459088994469417 /
    20470111135087704442718628728317306470400000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input86` at Taylor depth ten. -/
def sine86 : IntervalRat :=
  ⟨(32295972688773708440744521435784112185689967 /
    818804445403508177708745149132692258816000000 : ℚ),
   (6475190971466115620152998512114291843553309 /
    163760889080701635541749029826538451763200000 : ℚ),
   by decide +kernel⟩

theorem cosine86_eq :
    IntervalRat.cosComputable input86 10 = cosine86 := by gerver_interval_eq

theorem sine86_eq :
    IntervalRat.sinComputable input86 10 = sine86 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 87. -/
def input87 : IntervalRat :=
  ⟨(81 /
    2048 : ℚ),
   (203 /
    5120 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input87` at Taylor depth ten. -/
def cosine87 : IntervalRat :=
  ⟨(361148490445157692490995422188766073423341073579 /
    361432539137072766954740017916805120000000000000 : ℚ),
   (361149888158777126695139411648919957845491276421 /
    361432539137072766954740017916805120000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input87` at Taylor depth ten. -/
def sine87 : IntervalRat :=
  ⟨(14291194314211175663335605724654817064692473579 /
    361432539137072766954740017916805120000000000000 : ℚ),
   (14326499686139393402508140281011048576267526421 /
    361432539137072766954740017916805120000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine87_eq :
    IntervalRat.cosComputable input87 10 = cosine87 := by gerver_interval_eq

theorem sine87_eq :
    IntervalRat.sinComputable input87 10 = sine87 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 88. -/
def input88 : IntervalRat :=
  ⟨(203 /
    5120 : ℚ),
   (51 /
    1280 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input88` at Taylor depth ten. -/
def cosine88 : IntervalRat :=
  ⟨(3720536344721201270972986226411841454787 /
    3723491524413057858095022080000000000000 : ℚ),
   (119058087995104894265511986852395218401441 /
    119151728781217851459040706560000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input88` at Taylor depth ten. -/
def sine88 : IntervalRat :=
  ⟨(295183125710098218198847903082791734629 /
    7446983048826115716190044160000000000000 : ℚ),
   (296637997570037377479315346803916697371 /
    7446983048826115716190044160000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine88_eq :
    IntervalRat.cosComputable input88 10 = cosine88 := by gerver_interval_eq

theorem sine88_eq :
    IntervalRat.sinComputable input88 10 = sine88 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 89. -/
def input89 : IntervalRat :=
  ⟨(401 /
    10240 : ℚ),
   (201 /
    5120 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input89` at Taylor depth ten. -/
def cosine89 : IntervalRat :=
  ⟨(4458692088625402758674817003718901465189481937 /
    4462130112803367493268395282923520000000000000 : ℚ),
   (31210964218926368629467708323282222173937142041 /
    31234910789623572452878766980464640000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input89` at Taylor depth ten. -/
def sine89 : IntervalRat :=
  ⟨(174692832276385372468848397363828976921684497 /
    4462130112803367493268395282923520000000000000 : ℚ),
   (1225900891806627875312159270414225079724464521 /
    31234910789623572452878766980464640000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine89_eq :
    IntervalRat.cosComputable input89 10 = cosine89 := by gerver_interval_eq

theorem sine89_eq :
    IntervalRat.sinComputable input89 10 = sine89 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 90. -/
def input90 : IntervalRat :=
  ⟨(51 /
    1280 : ℚ),
   (103 /
    2560 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input90` at Taylor depth ten. -/
def cosine90 : IntervalRat :=
  ⟨(1234365348700446237058309938288792763925904713 /
    1235365124003666683927334045614080000000000000 : ℚ),
   (1234384670130822564457483086761446273080615607 /
    1235365124003666683927334045614080000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input90` at Taylor depth ten. -/
def sine90 : IntervalRat :=
  ⟨(49208300191084035845211228743188807018650953 /
    1235365124003666683927334045614080000000000000 : ℚ),
   (49690993635240274421952830266775403894629047 /
    1235365124003666683927334045614080000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine90_eq :
    IntervalRat.cosComputable input90 10 = cosine90 := by gerver_interval_eq

theorem sine90_eq :
    IntervalRat.sinComputable input90 10 = sine90 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 91. -/
def input91 : IntervalRat :=
  ⟨(103 /
    2560 : ℚ),
   (13 /
    320 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input91` at Taylor depth ten. -/
def cosine91 : IntervalRat :=
  ⟨(9196593195247565974558889421965581537 /
    9204187423018117874319360000000000000 : ℚ),
   (196197089185481121433662860509518344419 /
    196355998357719847985479680000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input91` at Taylor depth ten. -/
def sine91 : IntervalRat :=
  ⟨(7712976524636283329811259964585159 /
    191753904646210789048320000000000000 : ℚ),
   (1946975200159236605953184868869929 /
    47938476161552697262080000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine91_eq :
    IntervalRat.cosComputable input91 10 = cosine91 := by gerver_interval_eq

theorem sine91_eq :
    IntervalRat.sinComputable input91 10 = sine91 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 92. -/
def input92 : IntervalRat :=
  ⟨(49 /
    1280 : ℚ),
   (99 /
    2560 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input92` at Taylor depth ten. -/
def cosine92 : IntervalRat :=
  ⟨(1385456210932295119876947354892457887729951 /
    1386492843999625907887019130880000000000000 : ℚ),
   (1385477049791237589794359097692358219585249 /
    1386492843999625907887019130880000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input92` at Taylor depth ten. -/
def sine92 : IntervalRat :=
  ⟨(53063450668296993415734599470763252558111 /
    1386492843999625907887019130880000000000000 : ℚ),
   (53605183076541675369280812955342693553889 /
    1386492843999625907887019130880000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine92_eq :
    IntervalRat.cosComputable input92 10 = cosine92 := by gerver_interval_eq

theorem sine92_eq :
    IntervalRat.sinComputable input92 10 = sine92 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 93. -/
def input93 : IntervalRat :=
  ⟨(99 /
    2560 : ℚ),
   (199 /
    5120 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input93` at Taylor depth ten. -/
def cosine93 : IntervalRat :=
  ⟨(2528117008425923774554518883357414286800921808681 /
    2530027773959509368683180125417635840000000000000 : ℚ),
   (2528136166236756089128753923471827883884202389719 /
    2530027773959509368683180125417635840000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input93` at Taylor depth ten. -/
def sine93 : IntervalRat :=
  ⟨(97816285631204446173753733405981259965671509801 /
    2530027773959509368683180125417635840000000000000 : ℚ),
   (98310555479214168462356623239682386365241258199 /
    2530027773959509368683180125417635840000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine93_eq :
    IntervalRat.cosComputable input93 10 = cosine93 := by gerver_interval_eq

theorem sine93_eq :
    IntervalRat.sinComputable input93 10 = sine93 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 94. -/
def input94 : IntervalRat :=
  ⟨(199 /
    5120 : ℚ),
   (5 /
    128 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input94` at Taylor depth ten. -/
def cosine94 : IntervalRat :=
  ⟨(1836938592047975532920505076517 /
    1838340958338789708225199472640 : ℚ),
   (308608033845375280939017691317685829 /
    308841281000916670981833511403520000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input94` at Taylor depth ten. -/
def sine94 : IntervalRat :=
  ⟨(1627704465713632462502062657 /
    41889279649646900903568998400 : ℚ),
   (78522625730979890394633986087 /
    2010685423183051243371311923200 : ℚ),
   by decide +kernel⟩

theorem cosine94_eq :
    IntervalRat.cosComputable input94 10 = cosine94 := by gerver_interval_eq

theorem sine94_eq :
    IntervalRat.sinComputable input94 10 = sine94 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 95. -/
def input95 : IntervalRat :=
  ⟨(403 /
    10240 : ℚ),
   (101 /
    2560 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input95` at Taylor depth ten. -/
def cosine95 : IntervalRat :=
  ⟨(1234403794874191709841687972751785342426081989 /
    1235365124003666683927334045614080000000000000 : ℚ),
   (3291756129741183428204469314640938454094291571 /
    3294306997343111157139557454970880000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input95` at Taylor depth ten. -/
def sine95 : IntervalRat :=
  ⟨(16201920565087825434422353422693146021573633 /
    411788374667888894642444681871360000000000000 : ℚ),
   (16242144680971672792685093196530780869882367 /
    411788374667888894642444681871360000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine95_eq :
    IntervalRat.cosComputable input95 10 = cosine95 := by gerver_interval_eq

theorem sine95_eq :
    IntervalRat.sinComputable input95 10 = sine95 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 96. -/
def input96 : IntervalRat :=
  ⟨(99 /
    2560 : ℚ),
   (5 /
    128 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input96` at Taylor depth ten. -/
def cosine96 : IntervalRat :=
  ⟨(2410981899739895732156428127527 /
    2412822507819661492045574307840 : ℚ),
   (688862437830306157694705996261707 /
    689377859377046140584449802240000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input96` at Taylor depth ten. -/
def sine96 : IntervalRat :=
  ⟨(46642321324108665380561670311 /
    1206411253909830746022787153920 : ℚ),
   (235568471884287987322464063581 /
    6032056269549153730113935769600 : ℚ),
   by decide +kernel⟩

theorem cosine96_eq :
    IntervalRat.cosComputable input96 10 = cosine96 := by gerver_interval_eq

theorem sine96_eq :
    IntervalRat.sinComputable input96 10 = sine96 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 97. -/
def input97 : IntervalRat :=
  ⟨(201 /
    5120 : ℚ),
   (403 /
    10240 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input97` at Taylor depth ten. -/
def cosine97 : IntervalRat :=
  ⟨(5177484708108837129835130907194065562709403623198293 /
    5181496881069075187063152896855318200320000000000000 : ℚ),
   (5177504597487465469520304306642874777447590472642987 /
    5181496881069075187063152896855318200320000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input97` at Taylor depth ten. -/
def sine97 : IntervalRat :=
  ⟨(203361727284386073949042725464190739277393685319253 /
    5181496881069075187063152896855318200320000000000000 : ℚ),
   (203867863146484937878045817766715317893306520760747 /
    5181496881069075187063152896855318200320000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine97_eq :
    IntervalRat.cosComputable input97 10 = cosine97 := by gerver_interval_eq

theorem sine97_eq :
    IntervalRat.sinComputable input97 10 = sine97 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 98. -/
def input98 : IntervalRat :=
  ⟨(49 /
    1280 : ℚ),
   (5 /
    128 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input98` at Taylor depth ten. -/
def cosine98 : IntervalRat :=
  ⟨(133943438618270045865868459159 /
    134045694878870082891420794880 : ℚ),
   (150690924518356495176900213358783 /
    150801406738728843252848394240000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input98` at Taylor depth ten. -/
def sine98 : IntervalRat :=
  ⟨(76951977912712350686693389409 /
    2010685423183051243371311923200 : ℚ),
   (78523217426401986231661574047 /
    2010685423183051243371311923200 : ℚ),
   by decide +kernel⟩

theorem cosine98_eq :
    IntervalRat.cosComputable input98 10 = cosine98 := by gerver_interval_eq

theorem sine98_eq :
    IntervalRat.sinComputable input98 10 = sine98 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 99. -/
def input99 : IntervalRat :=
  ⟨(5 /
    128 : ℚ),
   (51 /
    1280 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input99` at Taylor depth ten. -/
def cosine99 : IntervalRat :=
  ⟨(7441072666725300214870879419434775206629 /
    7446983048826115716190044160000000000000 : ℚ),
   (7441302203252702704225404140637224793371 /
    7446983048826115716190044160000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input99` at Taylor depth ten. -/
def sine99 : IntervalRat :=
  ⟨(41545830475715126298376514423253600947 /
    1063854721260873673741434880000000000000 : ℚ),
   (42377182589799834911421424776746399053 /
    1063854721260873673741434880000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine99_eq :
    IntervalRat.cosComputable input99 10 = cosine99 := by gerver_interval_eq

theorem sine99_eq :
    IntervalRat.sinComputable input99 10 = sine99 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 100. -/
def input100 : IntervalRat :=
  ⟨(3 /
    80 : ℚ),
   (97 /
    2560 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input100` at Taylor depth ten. -/
def cosine100 : IntervalRat :=
  ⟨(1234478421398829838074065929568622208451133407 /
    1235365124003666683927334045614080000000000000 : ℚ),
   (1234496611818619712771211970375053167984066593 /
    1235365124003666683927334045614080000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input100` at Taylor depth ten. -/
def sine100 : IntervalRat :=
  ⟨(46315107847999366463243717387272146318049247 /
    1235365124003666683927334045614080000000000000 : ℚ),
   (46797786636873573831430647516607625628958753 /
    1235365124003666683927334045614080000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine100_eq :
    IntervalRat.cosComputable input100 10 = cosine100 := by gerver_interval_eq

theorem sine100_eq :
    IntervalRat.sinComputable input100 10 = sine100 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 101. -/
def input101 : IntervalRat :=
  ⟨(97 /
    2560 : ℚ),
   (39 /
    1024 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input101` at Taylor depth ten. -/
def cosine101 : IntervalRat :=
  ⟨(399516925150541993283511566213436901018921 /
    399806858107181727396848217349947392000000 : ℚ),
   (9987997288799972265020197201133144042845951 /
    9995171452679543184921205433748684800000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input101` at Taylor depth ten. -/
def sine101 : IntervalRat :=
  ⟨(15145269644066596029213517288335169064233 /
    399806858107181727396848217349947392000000 : ℚ),
   (3044675140737422942138708746864712108587 /
    79961371621436345479369643469989478400000 : ℚ),
   by decide +kernel⟩

theorem cosine101_eq :
    IntervalRat.cosComputable input101 10 = cosine101 := by gerver_interval_eq

theorem sine101_eq :
    IntervalRat.sinComputable input101 10 = sine101 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 102. -/
def input102 : IntervalRat :=
  ⟨(39 /
    1024 : ℚ),
   (49 /
    1280 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input102` at Taylor depth ten. -/
def cosine102 : IntervalRat :=
  ⟨(10763637416046819335210264725710950803171 /
    10771529052766345946632028160000000000000 : ℚ),
   (1377755871646289018325519123546809369028487 /
    1378755718754092281168899604480000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input102` at Taylor depth ten. -/
def sine102 : IntervalRat :=
  ⟨(3281148725155154700174281759794066715993 /
    86172232422130767573056225280000000000000 : ℚ),
   (3297983329349498220924392139550363284007 /
    86172232422130767573056225280000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine102_eq :
    IntervalRat.cosComputable input102 10 = cosine102 := by gerver_interval_eq

theorem sine102_eq :
    IntervalRat.sinComputable input102 10 = sine102 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 103. -/
def input103 : IntervalRat :=
  ⟨(49 /
    1280 : ℚ),
   (197 /
    5120 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input103` at Taylor depth ten. -/
def cosine103 : IntervalRat :=
  ⟨(842718406026918965255783979446573954961921577889 /
    843342591319836456227726708472545280000000000000 : ℚ),
   (2528174182865782648817083554489517109128691074333 /
    2530027773959509368683180125417635840000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input103` at Taylor depth ten. -/
def sine103 : IntervalRat :=
  ⟨(10758747773485376554149047367238465504232441483 /
    281114197106612152075908902824181760000000000000 : ℚ),
   (32440999109022986673090073224111882679628819551 /
    843342591319836456227726708472545280000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine103_eq :
    IntervalRat.cosComputable input103 10 = cosine103 := by gerver_interval_eq

theorem sine103_eq :
    IntervalRat.sinComputable input103 10 = sine103 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 104. -/
def input104 : IntervalRat :=
  ⟨(197 /
    5120 : ℚ),
   (99 /
    2560 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input104` at Taylor depth ten. -/
def cosine104 : IntervalRat :=
  ⟨(1385456212227468257863173698106574494061951 /
    1386492843999625907887019130880000000000000 : ℚ),
   (1385466658102192608442300680935385164977529 /
    1386492843999625907887019130880000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input104` at Taylor depth ten. -/
def sine104 : IntervalRat :=
  ⟨(53334182569428677984744864245574288206111 /
    1386492843999625907887019130880000000000000 : ℚ),
   (53605049114497447348405034300221592753889 /
    1386492843999625907887019130880000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine104_eq :
    IntervalRat.cosComputable input104 10 = cosine104 := by gerver_interval_eq

theorem sine104_eq :
    IntervalRat.sinComputable input104 10 = sine104 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 105. -/
def input105 : IntervalRat :=
  ⟨(5 /
    128 : ℚ),
   (101 /
    2560 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input105` at Taylor depth ten. -/
def cosine105 : IntervalRat :=
  ⟨(1234403793033583877659203370949621090834448899 /
    1235365124003666683927334045614080000000000000 : ℚ),
   (411474245820143472203155001134830217721850367 /
    411788374667888894642444681871360000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input105` at Taylor depth ten. -/
def sine105 : IntervalRat :=
  ⟨(16081310729785166166494046089387382278149633 /
    411788374667888894642444681871360000000000000 : ℚ),
   (2320315269056901151470564743202031103121481 /
    58826910666841270663206383124480000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine105_eq :
    IntervalRat.cosComputable input105 10 = cosine105 := by gerver_interval_eq

theorem sine105_eq :
    IntervalRat.sinComputable input105 10 = sine105 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 106. -/
def input106 : IntervalRat :=
  ⟨(101 /
    2560 : ℚ),
   (51 /
    1280 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input106` at Taylor depth ten. -/
def cosine106 : IntervalRat :=
  ⟨(7441072681832455112060059985955889148149 /
    7446983048826115716190044160000000000000 : ℚ),
   (1063026859750841892737552240091807932393 /
    1063854721260873673741434880000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input106` at Taylor depth ten. -/
def sine106 : IntervalRat :=
  ⟨(293729021582512639273396332973799078629 /
    7446983048826115716190044160000000000000 : ℚ),
   (296638761528860741941483474507438937371 /
    7446983048826115716190044160000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine106_eq :
    IntervalRat.cosComputable input106 10 = cosine106 := by gerver_interval_eq

theorem sine106_eq :
    IntervalRat.sinComputable input106 10 = sine106 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 107. -/
def input107 : IntervalRat :=
  ⟨(51 /
    1280 : ℚ),
   (13 /
    320 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input107` at Taylor depth ten. -/
def cosine107 : IntervalRat :=
  ⟨(82112439066518182679175654871865051 /
    82180244848376052449280000000000000 : ℚ),
   (9196882491646163938264590489074458513 /
    9204187423018117874319360000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input107` at Taylor depth ten. -/
def sine107 : IntervalRat :=
  ⟨(818367134370005781051199747246709 /
    20545061212094013112320000000000000 : ℚ),
   (5840956057377688189975235465286037 /
    143815428484658091786240000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine107_eq :
    IntervalRat.cosComputable input107 10 = cosine107 := by gerver_interval_eq

theorem sine107_eq :
    IntervalRat.sinComputable input107 10 = sine107 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 108. -/
def input108 : IntervalRat :=
  ⟨(199 /
    5120 : ℚ),
   (399 /
    10240 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input108` at Taylor depth ten. -/
def cosine108 : IntervalRat :=
  ⟨(9131506082811144729721225784899449533458333692983 /
    9138442471021296626213673539427368960000000000000 : ℚ),
   (9131540812476404121210352812092274780669154921417 /
    9138442471021296626213673539427368960000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input108` at Taylor depth ten. -/
def sine108 : IntervalRat :=
  ⟨(355095686486634419144547269144909015610135835703 /
    9138442471021296626213673539427368960000000000000 : ℚ),
   (355988337782595985839546520422186629654538980297 /
    9138442471021296626213673539427368960000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine108_eq :
    IntervalRat.cosComputable input108 10 = cosine108 := by gerver_interval_eq

theorem sine108_eq :
    IntervalRat.sinComputable input108 10 = sine108 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 109. -/
def input109 : IntervalRat :=
  ⟨(399 /
    10240 : ℚ),
   (5 /
    128 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input109` at Taylor depth ten. -/
def cosine109 : IntervalRat :=
  ⟨(617211367226596515773065292675977 /
    617682562001833341963667022807040 : ℚ),
   (19750839057704063271097533186685424149 /
    19765841984058666942837344729825280000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input109` at Taylor depth ten. -/
def sine109 : IntervalRat :=
  ⟨(1503861512218423046882569654081 /
    38605160125114583872729188925440 : ℚ),
   (471135157447586360571189656077 /
    12064112539098307460227871539200 : ℚ),
   by decide +kernel⟩

theorem cosine109_eq :
    IntervalRat.cosComputable input109 10 = cosine109 := by gerver_interval_eq

theorem sine109_eq :
    IntervalRat.sinComputable input109 10 = sine109 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 110. -/
def input110 : IntervalRat :=
  ⟨(99 /
    2560 : ℚ),
   (397 /
    10240 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input110` at Taylor depth ten. -/
def cosine110 : IntervalRat :=
  ⟨(5177603273114064359308644542010371937265350516826187 /
    5181496881069075187063152896855318200320000000000000 : ℚ),
   (5177622866005053397209231557228291347250488696741813 /
    5181496881069075187063152896855318200320000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input110` at Taylor depth ten. -/
def sine110 : IntervalRat :=
  ⟨(200328006155368709535837889519197071229017875177547 /
    5181496881069075187063152896855318200320000000000000 : ℚ),
   (200834138161190280136103111091201062396040092950453 /
    5181496881069075187063152896855318200320000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine110_eq :
    IntervalRat.cosComputable input110 10 = cosine110 := by gerver_interval_eq

theorem sine110_eq :
    IntervalRat.sinComputable input110 10 = sine110 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 111. -/
def input111 : IntervalRat :=
  ⟨(397 /
    10240 : ℚ),
   (199 /
    5120 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input111` at Taylor depth ten. -/
def cosine111 : IntervalRat :=
  ⟨(2528117009630215447843272049886226765864282040681 /
    2530027773959509368683180125417635840000000000000 : ℚ),
   (842708866866581508102147157016078230751667170893 /
    843342591319836456227726708472545280000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input111` at Taylor depth ten. -/
def sine111 : IntervalRat :=
  ⟨(32687765487614522192584714005509451799331527267 /
    843342591319836456227726708472545280000000000000 : ℚ),
   (1213709031397176866485479103816298473325427879 /
    31234910789623572452878766980464640000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine111_eq :
    IntervalRat.cosComputable input111 10 = cosine111 := by gerver_interval_eq

theorem sine111_eq :
    IntervalRat.sinComputable input111 10 = sine111 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 112. -/
def input112 : IntervalRat :=
  ⟨(197 /
    5120 : ℚ),
   (79 /
    2048 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input112` at Taylor depth ten. -/
def cosine112 : IntervalRat :=
  ⟨(9467688959568357943328922141006218917852039351 /
    9474737153954880342058336725678296137728000000 : ℚ),
   (552283935341410326756302516297542210480106368589 /
    552693000647368019953402975664567274700800000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input112` at Taylor depth ten. -/
def sine112 : IntervalRat :=
  ⟨(121488305016707968091985341018122783266871357 /
    3158245717984960114019445575226098712576000000 : ℚ),
   (170515525249114906180796613290112905245908497 /
    4421544005178944159627223805316538197606400000 : ℚ),
   by decide +kernel⟩

theorem cosine112_eq :
    IntervalRat.cosComputable input112 10 = cosine112 := by gerver_interval_eq

theorem sine112_eq :
    IntervalRat.sinComputable input112 10 = sine112 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 113. -/
def input113 : IntervalRat :=
  ⟨(79 /
    2048 : ℚ),
   (99 /
    2560 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input113` at Taylor depth ten. -/
def cosine113 : IntervalRat :=
  ⟨(1385456212877526531331122631901492608693861 /
    1386492843999625907887019130880000000000000 : ℚ),
   (11083691539409615894119701879530041647820987 /
    11091942751997007263096153047040000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input113` at Taylor depth ten. -/
def sine113 : IntervalRat :=
  ⟨(53469548520051534420566226254639079950111 /
    1386492843999625907887019130880000000000000 : ℚ),
   (53604981877822574482136916569418160049889 /
    1386492843999625907887019130880000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine113_eq :
    IntervalRat.cosComputable input113 10 = cosine113 := by gerver_interval_eq

theorem sine113_eq :
    IntervalRat.sinComputable input113 10 = sine113 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 114. -/
def input114 : IntervalRat :=
  ⟨(97 /
    2560 : ℚ),
   (49 /
    1280 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input114` at Taylor depth ten. -/
def cosine114 : IntervalRat :=
  ⟨(86109099250298692546989792625091248586953 /
    86172232422130767573056225280000000000000 : ℚ),
   (9567820140236202187571854014793557773963 /
    9574692491347863063672913920000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input114` at Taylor depth ten. -/
def sine114 : IntervalRat :=
  ⟨(1088107440281577805623514123442939449331 /
    28724077474043589191018741760000000000000 : ℚ),
   (366443498586794836166493814526865730223 /
    9574692491347863063672913920000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine114_eq :
    IntervalRat.cosComputable input114 10 = cosine114 := by gerver_interval_eq

theorem sine114_eq :
    IntervalRat.sinComputable input114 10 = sine114 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 115. -/
def input115 : IntervalRat :=
  ⟨(5 /
    128 : ℚ),
   (201 /
    5120 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input115` at Taylor depth ten. -/
def cosine115 : IntervalRat :=
  ⟨(31210844605056664047003750262841816962946639479 /
    31234910789623572452878766980464640000000000000 : ℚ),
   (31211083504274430963225992488432855165053360521 /
    31234910789623572452878766980464640000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input115` at Taylor depth ten. -/
def sine115 : IntervalRat :=
  ⟨(1219800325002194592765980943135119234946639479 /
    31234910789623572452878766980464640000000000000 : ℚ),
   (1225902452847426393011616468566435965053360521 /
    31234910789623572452878766980464640000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine115_eq :
    IntervalRat.cosComputable input115 10 = cosine115 := by gerver_interval_eq

theorem sine115_eq :
    IntervalRat.sinComputable input115 10 = sine115 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 116. -/
def input116 : IntervalRat :=
  ⟨(201 /
    5120 : ℚ),
   (101 /
    2560 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input116` at Taylor depth ten. -/
def cosine116 : IntervalRat :=
  ⟨(1234403794259127656322426607237315517983023139 /
    1235365124003666683927334045614080000000000000 : ℚ),
   (1234413290035271512230811409824354262017486661 /
    1235365124003666683927334045614080000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input116` at Taylor depth ten. -/
def sine116 : IntervalRat :=
  ⟨(48485151859924852207507779638918510325776899 /
    1235365124003666683927334045614080000000000000 : ℚ),
   (48726496400266752885976108494535143348207101 /
    1235365124003666683927334045614080000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine116_eq :
    IntervalRat.cosComputable input116 10 = cosine116 := by gerver_interval_eq

theorem sine116_eq :
    IntervalRat.sinComputable input116 10 = sine116 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 117. -/
def input117 : IntervalRat :=
  ⟨(399 /
    10240 : ℚ),
   (799 /
    20480 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input117` at Taylor depth ten. -/
def cosine117 : IntervalRat :=
  ⟨(10603630772843801313523010277413038866993890383850338721 /
    10611705612429465983105337132759691674255360000000000000 : ℚ),
   (10603650975115706061471241861722300148393632209325622879 /
    10611705612429465983105337132759691674255360000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input117` at Taylor depth ten. -/
def sine117 : IntervalRat :=
  ⟨(413378567513691126330235891261524253965855351339383201 /
    10611705612429465983105337132759691674255360000000000000 : ℚ),
   (413896848490322257896948029302495773251467288544904799 /
    10611705612429465983105337132759691674255360000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine117_eq :
    IntervalRat.cosComputable input117 10 = cosine117 := by gerver_interval_eq

theorem sine117_eq :
    IntervalRat.sinComputable input117 10 = sine117 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 118. -/
def input118 : IntervalRat :=
  ⟨(799 /
    20480 : ℚ),
   (5 /
    128 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input118` at Taylor depth ten. -/
def cosine118 : IntervalRat :=
  ⟨(3291793959339284049884026829895619 /
    3294306997343111157139557454970880 : ℚ),
   (180578755957256340526516712622400466147 /
    180716269568536383477370008958402560000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input118` at Taylor depth ten. -/
def sine118 : IntervalRat :=
  ⟨(80306456028117492045383655445831 /
    2058941873339444473212223409356800 : ℚ),
   (837573081629695472362891318363 /
    21447311180619213262627327180800 : ℚ),
   by decide +kernel⟩

theorem cosine118_eq :
    IntervalRat.cosComputable input118 10 = cosine118 := by gerver_interval_eq

theorem sine118_eq :
    IntervalRat.sinComputable input118 10 = sine118 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 119. -/
def input119 : IntervalRat :=
  ⟨(199 /
    5120 : ℚ),
   (797 /
    20480 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input119` at Taylor depth ten. -/
def cosine119 : IntervalRat :=
  ⟨(3534557047296445979321568732012693416620809152351766409 /
    3537235204143155327701779044253230558085120000000000000 : ℚ),
   (10603691293560685590776511322163579058973134966134204773 /
    10611705612429465983105337132759691674255360000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input119` at Taylor depth ten. -/
def sine119 : IntervalRat :=
  ⟨(137447684688966120492495619570546890033312894133536649 /
    3537235204143155327701779044253230558085120000000000000 : ℚ),
   (137620444795542478411013269970350834136848991148767351 /
    3537235204143155327701779044253230558085120000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine119_eq :
    IntervalRat.cosComputable input119 10 = cosine119 := by gerver_interval_eq

theorem sine119_eq :
    IntervalRat.sinComputable input119 10 = sine119 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 120. -/
def input120 : IntervalRat :=
  ⟨(797 /
    20480 : ℚ),
   (399 /
    10240 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input120` at Taylor depth ten. -/
def cosine120 : IntervalRat :=
  ⟨(9131506085006681481718550095077228696543473580983 /
    9138442471021296626213673539427368960000000000000 : ℚ),
   (9131523460733183870898304567356057296531414827177 /
    9138442471021296626213673539427368960000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input120` at Taylor depth ten. -/
def sine120 : IntervalRat :=
  ⟨(355541786612374525513582782773855915539567899703 /
    9138442471021296626213673539427368960000000000000 : ℚ),
   (355988112401869429823031153507130009713470180297 /
    9138442471021296626213673539427368960000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine120_eq :
    IntervalRat.cosComputable input120 10 = cosine120 := by gerver_interval_eq

theorem sine120_eq :
    IntervalRat.sinComputable input120 10 = sine120 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 121. -/
def input121 : IntervalRat :=
  ⟨(397 /
    10240 : ℚ),
   (159 /
    4096 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input121` at Taylor depth ten. -/
def cosine121 : IntervalRat :=
  ⟨(1675648222784835986558683308817214957829478289729 /
    1676911504186384747947510065423753746055168000000 : ℚ),
   (5984469283036941545688193257607605444174899888737 /
    5988969657808516956955393090799120521625600000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input121` at Taylor depth ten. -/
def sine121 : IntervalRat :=
  ⟨(64996746537781806481972551807481598262408712513 /
    1676911504186384747947510065423753746055168000000 : ℚ),
   (13015729504359519164955986111173882880420831987 /
    335382300837276949589502013084750749211033600000 : ℚ),
   by decide +kernel⟩

theorem cosine121_eq :
    IntervalRat.cosComputable input121 10 = cosine121 := by gerver_interval_eq

theorem sine121_eq :
    IntervalRat.sinComputable input121 10 = sine121 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 122. -/
def input122 : IntervalRat :=
  ⟨(159 /
    4096 : ℚ),
   (199 /
    5120 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input122` at Taylor depth ten. -/
def cosine122 : IntervalRat :=
  ⟨(2528117010233500274096538639196169795354515060301 /
    2530027773959509368683180125417635840000000000000 : ℚ),
   (10112487234937172169638973783919843333099332849421 /
    10120111095838037474732720501670543360000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input122` at Taylor depth ten. -/
def sine122 : IntervalRat :=
  ⟨(98186801878689610893648277429652288287482197801 /
    2530027773959509368683180125417635840000000000000 : ℚ),
   (98310369457934226437966941834906855555877802199 /
    2530027773959509368683180125417635840000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine122_eq :
    IntervalRat.cosComputable input122 10 = cosine122 := by gerver_interval_eq

theorem sine122_eq :
    IntervalRat.sinComputable input122 10 = sine122 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 123. -/
def input123 : IntervalRat :=
  ⟨(5 /
    128 : ℚ),
   (801 /
    20480 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input123` at Taylor depth ten. -/
def cosine123 : IntervalRat :=
  ⟨(130908522255235371629531702599743690917741301475120879 /
    131008711264561308433399223861230761410560000000000000 : ℚ),
   (130908772290697863720344490949388671416597770524879121 /
    131008711264561308433399223861230761410560000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input123` at Taylor depth ten. -/
def sine123 : IntervalRat :=
  ⟨(5116223173023498245844513292553025822851829475120879 /
    131008711264561308433399223861230761410560000000000000 : ℚ),
   (731803101675633954216522698708515265604938646411303 /
    18715530180651615490485603408747251630080000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine123_eq :
    IntervalRat.cosComputable input123 10 = cosine123 := by gerver_interval_eq

theorem sine123_eq :
    IntervalRat.sinComputable input123 10 = sine123 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 124. -/
def input124 : IntervalRat :=
  ⟨(801 /
    20480 : ℚ),
   (401 /
    10240 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input124` at Taylor depth ten. -/
def cosine124 : IntervalRat :=
  ⟨(5177524428548702465078679482313396757443195474324559 /
    5181496881069075187063152896855318200320000000000000 : ℚ),
   (739647761428605124838221554226139452841433614642663 /
    740213840152725026723307556693616885760000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input124` at Taylor depth ten. -/
def sine124 : IntervalRat :=
  ⟨(202603432755288433540214186916795469898438278043599 /
    5181496881069075187063152896855318200320000000000000 : ℚ),
   (202856500121047242556812005975351888738685977700401 /
    5181496881069075187063152896855318200320000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine124_eq :
    IntervalRat.cosComputable input124 10 = cosine124 := by gerver_interval_eq

theorem sine124_eq :
    IntervalRat.sinComputable input124 10 = sine124 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 125. -/
def input125 : IntervalRat :=
  ⟨(27 /
    640 : ℚ),
   (11 /
    256 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input125` at Taylor depth ten. -/
def cosine125 : IntervalRat :=
  ⟨(701264123578975768914345776902680119 /
    701912002274810615867803435008000000 : ℚ),
   (17532186802311203876237254891867778209 /
    17547800056870265396695085875200000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input125` at Taylor depth ten. -/
def sine125 : IntervalRat :=
  ⟨(29602801261267208973686975536250423 /
    701912002274810615867803435008000000 : ℚ),
   (6030267140687004072499860733909493 /
    140382400454962123173560687001600000 : ℚ),
   by decide +kernel⟩

theorem cosine125_eq :
    IntervalRat.cosComputable input125 10 = cosine125 := by gerver_interval_eq

theorem sine125_eq :
    IntervalRat.sinComputable input125 10 = sine125 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 126. -/
def input126 : IntervalRat :=
  ⟨(11 /
    256 : ℚ),
   (7 /
    160 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input126` at Taylor depth ten. -/
def cosine126 : IntervalRat :=
  ⟨(47512504563688345783676042321389 /
    47558012065032437760000000000000 : ℚ),
   (82104391701747955049547933151849183 /
    82180244848376052449280000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input126` at Taylor depth ten. -/
def sine126 : IntervalRat :=
  ⟨(2298213551984782949851791251797 /
    53502763573161492480000000000000 : ℚ),
   (10833452238294522380076661233 /
    247697979505377280000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine126_eq :
    IntervalRat.cosComputable input126 10 = cosine126 := by gerver_interval_eq

theorem sine126_eq :
    IntervalRat.sinComputable input126 10 = sine126 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 127. -/
def input127 : IntervalRat :=
  ⟨(803 /
    20480 : ℚ),
   (1607 /
    40960 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input127` at Taylor depth ten. -/
def cosine127 : IntervalRat :=
  ⟨(3102292721096146790914345409943381095573125265251501409231 /
    3104681870607935190485675778270264078410711040000000000000 : ℚ),
   (7238689952620004306919486169166541226493778751886295103261 /
    7244257698085182111133243482630616182958325760000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input127` at Taylor depth ten. -/
def sine127 : IntervalRat :=
  ⟨(10517300887030309845653337382823429760753984052103739097 /
    268305840669821559671601610467800599368826880000000000000 : ℚ),
   (31571559006441249139499610110905747057644199055286606709 /
    804917522009464679014804831403401798106480640000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine127_eq :
    IntervalRat.cosComputable input127 10 = cosine127 := by gerver_interval_eq

theorem sine127_eq :
    IntervalRat.sinComputable input127 10 = sine127 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 128. -/
def input128 : IntervalRat :=
  ⟨(1607 /
    40960 : ℚ),
   (201 /
    5120 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input128` at Taylor depth ten. -/
def cosine128 : IntervalRat :=
  ⟨(124843378527575162591592181377466606841654836261 /
    124939643158494289811515067921858560000000000000 : ℚ),
   (7989983887221021524391667007713856875814545098281 /
    7996137162143634547936964346998947840000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input128` at Taylor depth ten. -/
def sine128 : IntervalRat :=
  ⟨(1225136951634664621074188601578125618654775479 /
    31234910789623572452878766980464640000000000000 : ℚ),
   (1225899718468143754666955926811978034386544521 /
    31234910789623572452878766980464640000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine128_eq :
    IntervalRat.cosComputable input128 10 = cosine128 := by gerver_interval_eq

theorem sine128_eq :
    IntervalRat.sinComputable input128 10 = sine128 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 129. -/
def input129 : IntervalRat :=
  ⟨(101 /
    2560 : ℚ),
   (203 /
    5120 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input129` at Taylor depth ten. -/
def cosine129 : IntervalRat :=
  ⟨(120382830087506161818228819130772512495313368313 /
    120477513045690922318246672638935040000000000000 : ℚ),
   (361151282242867939372142329277475652660651106581 /
    361432539137072766954740017916805120000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input129` at Taylor depth ten. -/
def sine129 : IntervalRat :=
  ⟨(1583989712580972714783900869507234648341019731 /
    40159171015230307439415557546311680000000000000 : ℚ),
   (1591835345724829241716046962001838448526820269 /
    40159171015230307439415557546311680000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine129_eq :
    IntervalRat.cosComputable input129 10 = cosine129 := by gerver_interval_eq

theorem sine129_eq :
    IntervalRat.sinComputable input129 10 = sine129 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 130. -/
def input130 : IntervalRat :=
  ⟨(399 /
    10240 : ℚ),
   (1597 /
    40960 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input130` at Taylor depth ten. -/
def cosine130 : IntervalRat :=
  ⟨(21716256513769351835344939325561641993836788950545747157307 /
    21732773094255546333399730447891848548874977280000000000000 : ℚ),
   (21716277194418910988236046845741945384321842172602069802693 /
    21732773094255546333399730447891848548874977280000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input130` at Taylor depth ten. -/
def sine130 : IntervalRat :=
  ⟨(846599575021975482932776507993739176963989365303236370747 /
    21732773094255546333399730447891848548874977280000000000000 : ℚ),
   (847130294657909553360479374092520787253380223566653677253 /
    21732773094255546333399730447891848548874977280000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine130_eq :
    IntervalRat.cosComputable input130 10 = cosine130 := by gerver_interval_eq

theorem sine130_eq :
    IntervalRat.sinComputable input130 10 = sine130 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 131. -/
def input131 : IntervalRat :=
  ⟨(1597 /
    40960 : ℚ),
   (799 /
    20480 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input131` at Taylor depth ten. -/
def cosine131 : IntervalRat :=
  ⟨(10603630774124551992411547025898258952581365815680258721 /
    10611705612429465983105337132759691674255360000000000000 : ℚ),
   (3534546959474346395146908305277819826933044677844011573 /
    3537235204143155327701779044253230558085120000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input131` at Taylor depth ten. -/
def sine131 : IntervalRat :=
  ⟨(15319910246340489586807496486775936917274594546360563 /
    393026133793683925300197671583692284231680000000000000 : ℚ),
   (45988524131182489207728765097940529415618688337878311 /
    1179078401381051775900593014751076852695040000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine131_eq :
    IntervalRat.cosComputable input131 10 = cosine131 := by gerver_interval_eq

theorem sine131_eq :
    IntervalRat.sinComputable input131 10 = sine131 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 132. -/
def input132 : IntervalRat :=
  ⟨(799 /
    20480 : ℚ),
   (1599 /
    40960 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input132` at Taylor depth ten. -/
def cosine132 : IntervalRat :=
  ⟨(268101421285196564628556889783154368729092559889162776561 /
    268305840669821559671601610467800599368826880000000000000 : ℚ),
   (268101676921703285502615359339476737693447974163091738639 /
    268305840669821559671601610467800599368826880000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input132` at Taylor depth ten. -/
def sine132 : IntervalRat :=
  ⟨(10464937511557683447554690825374630276128625511772532721 /
    268305840669821559671601610467800599368826880000000000000 : ℚ),
   (10471489609987254475651414253664454016070977982942859279 /
    268305840669821559671601610467800599368826880000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine132_eq :
    IntervalRat.cosComputable input132 10 = cosine132 := by gerver_interval_eq

theorem sine132_eq :
    IntervalRat.sinComputable input132 10 = sine132 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 133. -/
def input133 : IntervalRat :=
  ⟨(1599 /
    40960 : ℚ),
   (5 /
    128 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input133` at Taylor depth ten. -/
def cosine133 : IntervalRat :=
  ⟨(22572301438206010512436190529025711 /
    22589533696067047934671251119800320 : ℚ),
   (80899205540722865406812088912038731205749 /
    80960888766704299797861764013364346880000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input133` at Taylor depth ten. -/
def sine133 : IntervalRat :=
  ⟨(1542848839354056347036542240528369 /
    39531683968117333885674689459650560 : ℚ),
   (120610485442772053221531987345427 /
    3088412810009166709818335114035200 : ℚ),
   by decide +kernel⟩

theorem cosine133_eq :
    IntervalRat.cosComputable input133 10 = cosine133 := by gerver_interval_eq

theorem sine133_eq :
    IntervalRat.sinComputable input133 10 = sine133 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 134. -/
def input134 : IntervalRat :=
  ⟨(5 /
    128 : ℚ),
   (1601 /
    40960 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input134` at Taylor depth ten. -/
def cosine134 : IntervalRat :=
  ⟨(21716173682656975419871850469952001387272257600860019182399 /
    21732773094255546333399730447891848548874977280000000000000 : ℚ),
   (7238731471707168350918458585301615781064429906827993605867 /
    7244257698085182111133243482630616182958325760000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input134` at Taylor depth ten. -/
def sine134 : IntervalRat :=
  ⟨(94302255536505206184715955471938600233124546257335464711 /
    2414752566028394037044414494210205394319441920000000000000 : ℚ),
   (283083673379541718587875880114432021981516114827993605867 /
    7244257698085182111133243482630616182958325760000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine134_eq :
    IntervalRat.cosComputable input134 10 = cosine134 := by gerver_interval_eq

theorem sine134_eq :
    IntervalRat.sinComputable input134 10 = sine134 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 135. -/
def input135 : IntervalRat :=
  ⟨(1601 /
    40960 : ℚ),
   (801 /
    20480 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input135` at Taylor depth ten. -/
def cosine135 : IntervalRat :=
  ⟨(130908522271166175634637772308389863473710653399945199 /
    131008711264561308433399223861230761410560000000000000 : ℚ),
   (130908647327941061434076306073008449326623043391973201 /
    131008711264561308433399223861230761410560000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input135` at Taylor depth ten. -/
def sine135 : IntervalRat :=
  ⟨(5119420812631176939929839645176637463755398850352879 /
    131008711264561308433399223861230761410560000000000000 : ℚ),
   (5122620082493240637461146792612622366616909633743121 /
    131008711264561308433399223861230761410560000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine135_eq :
    IntervalRat.cosComputable input135 10 = cosine135 := by gerver_interval_eq

theorem sine135_eq :
    IntervalRat.sinComputable input135 10 = sine135 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 136. -/
def input136 : IntervalRat :=
  ⟨(801 /
    20480 : ℚ),
   (1603 /
    40960 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input136` at Taylor depth ten. -/
def cosine136 : IntervalRat :=
  ⟨(3102304598491087380490140353243844620484365208405632184659 /
    3104681870607935190485675778270264078410711040000000000000 : ℚ),
   (3102307563972803791798879488390377272968194855752886947501 /
    3104681870607935190485675778270264078410711040000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input136` at Taylor depth ten. -/
def sine136 : IntervalRat :=
  ⟨(121397237028081553279497237916419310675438248960757821779 /
    3104681870607935190485675778270264078410711040000000000000 : ℚ),
   (121473054263479154906104734946963526540826860794900418221 /
    3104681870607935190485675778270264078410711040000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine136_eq :
    IntervalRat.cosComputable input136 10 = cosine136 := by gerver_interval_eq

theorem sine136_eq :
    IntervalRat.sinComputable input136 10 = sine136 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 137. -/
def input137 : IntervalRat :=
  ⟨(1603 /
    40960 : ℚ),
   (401 /
    10240 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input137` at Taylor depth ten. -/
def cosine137 : IntervalRat :=
  ⟨(5177524429181141649500726146611216065003813508951959 /
    5181496881069075187063152896855318200320000000000000 : ℚ),
   (383520694922304800686036759984576010680477470630841 /
    383814583782894458300974288655949496320000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input137` at Taylor depth ten. -/
def sine137 : IntervalRat :=
  ⟨(7508514882199511901111187422608274399115671775837 /
    191907291891447229150487144327974748160000000000000 : ℚ),
   (67618811840808811871515986375227402889889889313467 /
    1727165627023025062354384298951772733440000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine137_eq :
    IntervalRat.cosComputable input137 10 = cosine137 := by gerver_interval_eq

theorem sine137_eq :
    IntervalRat.sinComputable input137 10 = sine137 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 138. -/
def input138 : IntervalRat :=
  ⟨(13 /
    320 : ℚ),
   (21 /
    512 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input138` at Taylor depth ten. -/
def cosine138 : IntervalRat :=
  ⟨(27864858434474474892594258360078491989 /
    27888313205021046832927470518272000000 : ℚ),
   (696632578143784788060087866845157260979 /
    697207830125526170823186762956800000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input138` at Taylor depth ten. -/
def sine138 : IntervalRat :=
  ⟨(1132645089795438496251581798341468501 /
    27888313205021046832927470518272000000 : ℚ),
   (228708397546014656542320430045188847 /
    5577662641004209366585494103654400000 : ℚ),
   by decide +kernel⟩

theorem cosine138_eq :
    IntervalRat.cosComputable input138 10 = cosine138 := by gerver_interval_eq

theorem sine138_eq :
    IntervalRat.sinComputable input138 10 = sine138 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 139. -/
def input139 : IntervalRat :=
  ⟨(21 /
    512 : ℚ),
   (53 /
    1280 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input139` at Taylor depth ten. -/
def cosine139 : IntervalRat :=
  ⟨(602688608192434169105455355705063250858403 /
    603205626954915373011393576960000000000000 : ℚ),
   (602698318610243250762606614963720606254097 /
    603205626954915373011393576960000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input139` at Taylor depth ten. -/
def sine139 : IntervalRat :=
  ⟨(24733786780776137648644719812107427808403 /
    603205626954915373011393576960000000000000 : ℚ),
   (24969480678873956378342432557633692191597 /
    603205626954915373011393576960000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine139_eq :
    IntervalRat.cosComputable input139 10 = cosine139 := by gerver_interval_eq

theorem sine139_eq :
    IntervalRat.sinComputable input139 10 = sine139 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 140. -/
def input140 : IntervalRat :=
  ⟨(53 /
    1280 : ℚ),
   (107 /
    2560 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input140` at Taylor depth ten. -/
def cosine140 : IntervalRat :=
  ⟨(1234286199849888995795817523346011811391992717 /
    1235365124003666683927334045614080000000000000 : ℚ),
   (19592163099798858956333389185535584182273741 /
    19608970222280423554402127708160000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input140` at Taylor depth ten. -/
def sine140 : IntervalRat :=
  ⟨(17045648304537606595881748954022337818915119 /
    411788374667888894642444681871360000000000000 : ℚ),
   (5735516513231135181390746472062117747273627 /
    137262791555962964880814893957120000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine140_eq :
    IntervalRat.cosComputable input140 10 = cosine140 := by gerver_interval_eq

theorem sine140_eq :
    IntervalRat.sinComputable input140 10 = sine140 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 141. -/
def input141 : IntervalRat :=
  ⟨(107 /
    2560 : ℚ),
   (27 /
    640 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input141` at Taylor depth ten. -/
def cosine141 : IntervalRat :=
  ⟨(7265973631440921884690381443721644939 /
    7272444383619253629091840000000000000 : ℚ),
   (116257486764622111512294007482602725361 /
    116359110137908058065469440000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input141` at Taylor depth ten. -/
def sine141 : IntervalRat :=
  ⟨(151937645594902036742764296606223117 /
    3636222191809626814545920000000000000 : ℚ),
   (21908351765486039891038153606405269 /
    519460313115660973506560000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine141_eq :
    IntervalRat.cosComputable input141 10 = cosine141 := by gerver_interval_eq

theorem sine141_eq :
    IntervalRat.sinComputable input141 10 = sine141 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 142. -/
def input142 : IntervalRat :=
  ⟨(23 /
    640 : ℚ),
   (47 /
    1280 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input142` at Taylor depth ten. -/
def cosine142 : IntervalRat :=
  ⟨(7441963329845303952802829911879490976417 /
    7446983048826115716190044160000000000000 : ℚ),
   (602816149506159240942410868018314609214223 /
    603205626954915373011393576960000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input142` at Taylor depth ten. -/
def sine142 : IntervalRat :=
  ⟨(7224277104308498955951450444532113243899 /
    201068542318305124337131192320000000000000 : ℚ),
   (2460465484311995730544572986421119713367 /
    67022847439435041445710397440000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine142_eq :
    IntervalRat.cosComputable input142 10 = cosine142 := by gerver_interval_eq

theorem sine142_eq :
    IntervalRat.sinComputable input142 10 = sine142 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 143. -/
def input143 : IntervalRat :=
  ⟨(47 /
    1280 : ℚ),
   (3 /
    80 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input143` at Taylor depth ten. -/
def cosine143 : IntervalRat :=
  ⟨(1732666855015318342257421679953 /
    1733885856537640960000000000000 : ℚ),
   (443575583568080760988205872872617 /
    443874779273636085760000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input143` at Taylor depth ten. -/
def sine143 : IntervalRat :=
  ⟨(31825600276727018480388105649 /
    866942928268820480000000000000 : ℚ),
   (2031440930312822113741764061 /
    54183933016801280000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine143_eq :
    IntervalRat.cosComputable input143 10 = cosine143 := by gerver_interval_eq

theorem sine143_eq :
    IntervalRat.sinComputable input143 10 = sine143 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 144. -/
def input144 : IntervalRat :=
  ⟨(21 /
    640 : ℚ),
   (43 /
    1280 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input144` at Taylor depth ten. -/
def cosine144 : IntervalRat :=
  ⟨(602865286641507842031669378438012213712973 /
    603205626954915373011393576960000000000000 : ℚ),
   (602880933760179784208597705786924402571187 /
    603205626954915373011393576960000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input144` at Taylor depth ten. -/
def sine144 : IntervalRat :=
  ⟨(19788962028680876151905109970553425545293 /
    603205626954915373011393576960000000000000 : ℚ),
   (20260303006399139982848493415458386294707 /
    603205626954915373011393576960000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine144_eq :
    IntervalRat.cosComputable input144 10 = cosine144 := by gerver_interval_eq

theorem sine144_eq :
    IntervalRat.sinComputable input144 10 = sine144 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 145. -/
def input145 : IntervalRat :=
  ⟨(43 /
    1280 : ℚ),
   (11 /
    320 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input145` at Taylor depth ten. -/
def cosine145 : IntervalRat :=
  ⟨(1935763870691727827891152904110733 /
    1936908127739502919680000000000000 : ℚ),
   (836272207945510570393626113081652419 /
    836744311183465261301760000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input145` at Taylor depth ten. -/
def sine145 : IntervalRat :=
  ⟨(20910597955442336261875671378019 /
    622577612487697367040000000000000 : ℚ),
   (21397080333023598946011376648981 /
    622577612487697367040000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine145_eq :
    IntervalRat.cosComputable input145 10 = cosine145 := by gerver_interval_eq

theorem sine145_eq :
    IntervalRat.sinComputable input145 10 = sine145 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 146. -/
def input146 : IntervalRat :=
  ⟨(11 /
    320 : ℚ),
   (9 /
    256 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input146` at Taylor depth ten. -/
def cosine146 : IntervalRat :=
  ⟨(13608926003683372896546691323370817 /
    13617340432139183023890366464000000 : ℚ),
   (2381626775399867046301654164086882449 /
    2383034575624357029180814131200000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input146` at Taylor depth ten. -/
def sine146 : IntervalRat :=
  ⟨(467999658230968941251590308666689 /
    13617340432139183023890366464000000 : ℚ),
   (670096487685589570935957399662757 /
    19064276604994856233446513049600000 : ℚ),
   by decide +kernel⟩

theorem cosine146_eq :
    IntervalRat.cosComputable input146 10 = cosine146 := by gerver_interval_eq

theorem sine146_eq :
    IntervalRat.sinComputable input146 10 = sine146 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 147. -/
def input147 : IntervalRat :=
  ⟨(9 /
    256 : ℚ),
   (23 /
    640 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input147` at Taylor depth ten. -/
def cosine147 : IntervalRat :=
  ⟨(294343821221139977031455534760616611073 /
    294533997536579771978219520000000000000 : ℚ),
   (294352000723671310093531013638968695177 /
    294533997536579771978219520000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input147` at Taylor depth ten. -/
def sine147 : IntervalRat :=
  ⟨(10352482130378339312924879242642086073 /
    294533997536579771978219520000000000000 : ℚ),
   (10582635272455016294291472658237913927 /
    294533997536579771978219520000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine147_eq :
    IntervalRat.cosComputable input147 10 = cosine147 := by gerver_interval_eq

theorem sine147_eq :
    IntervalRat.sinComputable input147 10 = sine147 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 148. -/
def input148 : IntervalRat :=
  ⟨(47 /
    1280 : ℚ),
   (19 /
    512 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input148` at Taylor depth ten. -/
def cosine148 : IntervalRat :=
  ⟨(15801786948935920416886267975488611691013 /
    15812673587246933554269875783860224000000 : ℚ),
   (18811922572219149224942458207551716867383 /
    18824611413389206612226042599833600000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input148` at Taylor depth ten. -/
def sine148 : IntervalRat :=
  ⟨(193496118125386163724083536181594784599 /
    5270891195748977851423291927953408000000 : ℚ),
   (39111105523933561167915022950645137237 /
    1054178239149795570284658385590681600000 : ℚ),
   by decide +kernel⟩

theorem cosine148_eq :
    IntervalRat.cosComputable input148 10 = cosine148 := by gerver_interval_eq

theorem sine148_eq :
    IntervalRat.sinComputable input148 10 = sine148 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 149. -/
def input149 : IntervalRat :=
  ⟨(19 /
    512 : ℚ),
   (3 /
    80 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input149` at Taylor depth ten. -/
def cosine149 : IntervalRat :=
  ⟨(27722669727121390447656138613393 /
    27742173704602255360000000000000 : ℚ),
   (28388427765822779031384535913101193 /
    28407985873512709488640000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input149` at Taylor depth ten. -/
def sine149 : IntervalRat :=
  ⟨(1029253456105894848092144563393 /
    27742173704602255360000000000000 : ℚ),
   (32502898634343941259988307101 /
    866942928268820480000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine149_eq :
    IntervalRat.cosComputable input149 10 = cosine149 := by gerver_interval_eq

theorem sine149_eq :
    IntervalRat.sinComputable input149 10 = sine149 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 150. -/
def input150 : IntervalRat :=
  ⟨(23 /
    640 : ℚ),
   (93 /
    2560 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input150` at Taylor depth ten. -/
def cosine150 : IntervalRat :=
  ⟨(15241358467642863119566570858769634576973163 /
    15251421283995884986757210439680000000000000 : ℚ),
   (2177367675999662490064667008335483244939651 /
    2178774469142269283822458634240000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input150` at Taylor depth ten. -/
def sine150 : IntervalRat :=
  ⟨(547977403049699276374141345973538526346603 /
    15251421283995884986757210439680000000000000 : ℚ),
   (553936285886593746093868059820851325813397 /
    15251421283995884986757210439680000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine150_eq :
    IntervalRat.cosComputable input150 10 = cosine150 := by gerver_interval_eq

theorem sine150_eq :
    IntervalRat.sinComputable input150 10 = sine150 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 151. -/
def input151 : IntervalRat :=
  ⟨(93 /
    2560 : ℚ),
   (47 /
    1280 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input151` at Taylor depth ten. -/
def cosine151 : IntervalRat :=
  ⟨(602799030674007557119804133059706540674177 /
    603205626954915373011393576960000000000000 : ℚ),
   (602807636589290615026676983737287991743123 /
    603205626954915373011393576960000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input151` at Taylor depth ten. -/
def sine151 : IntervalRat :=
  ⟨(21908405573276796150311800426641357843697 /
    603205626954915373011393576960000000000000 : ℚ),
   (3163440737081408546882057361244826694329 /
    86172232422130767573056225280000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine151_eq :
    IntervalRat.cosComputable input151 10 = cosine151 := by gerver_interval_eq

theorem sine151_eq :
    IntervalRat.sinComputable input151 10 = sine151 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 152. -/
def input152 : IntervalRat :=
  ⟨(3 /
    80 : ℚ),
   (193 /
    5120 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input152` at Taylor depth ten. -/
def cosine152 : IntervalRat :=
  ⟨(361175782868959572020314813911312411803966364809 /
    361432539137072766954740017916805120000000000000 : ℚ),
   (2528249058816130337418001794142295359322471462977 /
    2530027773959509368683180125417635840000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input152` at Taylor depth ten. -/
def sine152 : IntervalRat :=
  ⟨(94853574296867659818782357188834089892609066943 /
    2530027773959509368683180125417635840000000000000 : ℚ),
   (95347836773383728388945328729853300064879573057 /
    2530027773959509368683180125417635840000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine152_eq :
    IntervalRat.cosComputable input152 10 = cosine152 := by gerver_interval_eq

theorem sine152_eq :
    IntervalRat.sinComputable input152 10 = sine152 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 153. -/
def input153 : IntervalRat :=
  ⟨(193 /
    5120 : ℚ),
   (97 /
    2560 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input153` at Taylor depth ten. -/
def cosine153 : IntervalRat :=
  ⟨(411492807494708158316648635774206143073706069 /
    411788374667888894642444681871360000000000000 : ℚ),
   (1234487541256739881464028803260836804799180393 /
    1235365124003666683927334045614080000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input153` at Taylor depth ten. -/
def sine153 : IntervalRat :=
  ⟨(5172925819580360644636072145526997889788583 /
    137262791555962964880814893957120000000000000 : ℚ),
   (5199741340922756444940859660420944434435417 /
    137262791555962964880814893957120000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine153_eq :
    IntervalRat.cosComputable input153 10 = cosine153 := by gerver_interval_eq

theorem sine153_eq :
    IntervalRat.sinComputable input153 10 = sine153 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 154. -/
def input154 : IntervalRat :=
  ⟨(1 /
    5 : ℚ),
   (3 /
    10 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input154` at Taylor depth ten. -/
def cosine154 : IntervalRat :=
  ⟨(47069769839821973 /
    49280000000000000 : ℚ),
   (48301782159835147 /
    49280000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input154` at Taylor depth ten. -/
def sine154 : IntervalRat :=
  ⟨(9708455046749813 /
    49280000000000000 : ℚ),
   (14685883098130187 /
    49280000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine154_eq :
    IntervalRat.cosComputable input154 10 = cosine154 := by gerver_interval_eq

theorem sine154_eq :
    IntervalRat.sinComputable input154 10 = sine154 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 155. -/
def input155 : IntervalRat :=
  ⟨(3 /
    10 : ℚ),
   (2 /
    5 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input155` at Taylor depth ten. -/
def cosine155 : IntervalRat :=
  ⟨(128164336464563 /
    139218750000000 : ℚ),
   (7450082506813097 /
    7796250000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input155` at Taylor depth ten. -/
def sine155 : IntervalRat :=
  ⟨(569196149282077 /
    1949062500000000 : ℚ),
   (192005994993137 /
    487265625000000 : ℚ),
   by decide +kernel⟩

theorem cosine155_eq :
    IntervalRat.cosComputable input155 10 = cosine155 := by gerver_interval_eq

theorem sine155_eq :
    IntervalRat.sinComputable input155 10 = sine155 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 156. -/
def input156 : IntervalRat :=
  ⟨(203 /
    5120 : ℚ),
   (407 /
    10240 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input156` at Taylor depth ten. -/
def cosine156 : IntervalRat :=
  ⟨(470673152476434187615150906452292431131468557226827 /
    471045171006279562460286626986847109120000000000000 : ℚ),
   (156891659523570634202152724945068035715111100239591 /
    157015057002093187486762208995615703040000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input156` at Taylor depth ten. -/
def sine156 : IntervalRat :=
  ⟨(6223762704509829648077944124238193568730641051929 /
    157015057002093187486762208995615703040000000000000 : ℚ),
   (2079700077918793956765616662075169717340319521357 /
    52338352334031062495587402998538567680000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine156_eq :
    IntervalRat.cosComputable input156 10 = cosine156 := by gerver_interval_eq

theorem sine156_eq :
    IntervalRat.sinComputable input156 10 = sine156 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 157. -/
def input157 : IntervalRat :=
  ⟨(407 /
    10240 : ℚ),
   (51 /
    1280 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input157` at Taylor depth ten. -/
def cosine157 : IntervalRat :=
  ⟨(119057163092183500035411148489980183453409 /
    119151728781217851459040706560000000000000 : ℚ),
   (7619688073110813700702201242517681118010809 /
    7625710641997942493378605219840000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input157` at Taylor depth ten. -/
def sine157 : IntervalRat :=
  ⟨(42272882539175140676045315455524766447 /
    1063854721260873673741434880000000000000 : ℚ),
   (42376802025126730949837379196879931053 /
    1063854721260873673741434880000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine157_eq :
    IntervalRat.cosComputable input157 10 = cosine157 := by gerver_interval_eq

theorem sine157_eq :
    IntervalRat.sinComputable input157 10 = sine157 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 158. -/
def input158 : IntervalRat :=
  ⟨(51 /
    1280 : ℚ),
   (41 /
    1024 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input158` at Taylor depth ten. -/
def cosine158 : IntervalRat :=
  ⟨(32358400830924491902713825354763765421763991 /
    32384355506681719919144705605345738752000000 : ℚ),
   (808966336577353415584532193207653948963736641 /
    809608887667042997978617640133643468800000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input158` at Taylor depth ten. -/
def sine158 : IntervalRat :=
  ⟨(1289969435939715235938186456924344435404183 /
    32384355506681719919144705605345738752000000 : ℚ),
   (259259237449210273535955983901467251927573 /
    6476871101336343983828941121069147750400000 : ℚ),
   by decide +kernel⟩

theorem cosine158_eq :
    IntervalRat.cosComputable input158 10 = cosine158 := by gerver_interval_eq

theorem sine158_eq :
    IntervalRat.sinComputable input158 10 = sine158 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 159. -/
def input159 : IntervalRat :=
  ⟨(41 /
    1024 : ℚ),
   (103 /
    2560 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input159` at Taylor depth ten. -/
def cosine159 : IntervalRat :=
  ⟨(411455116666810636363037028305532994539439651 /
    411788374667888894642444681871360000000000000 : ℚ),
   (1234375034278340723346441673303811000898906047 /
    1235365124003666683927334045614080000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input159` at Taylor depth ten. -/
def sine159 : IntervalRat :=
  ⟨(5494390817699296599533669429011549904913217 /
    137262791555962964880814893957120000000000000 : ℚ),
   (16563621465811003295437788277794620045260349 /
    411788374667888894642444681871360000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine159_eq :
    IntervalRat.cosComputable input159 10 = cosine159 := by gerver_interval_eq

theorem sine159_eq :
    IntervalRat.sinComputable input159 10 = sine159 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 160. -/
def input160 : IntervalRat :=
  ⟨(7 /
    160 : ℚ),
   (57 /
    1280 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input160` at Taylor depth ten. -/
def cosine160 : IntervalRat :=
  ⟨(7439600422815169659012065063621350396327 /
    7446983048826115716190044160000000000000 : ℚ),
   (7439857231010173862253345149175815990873 /
    7446983048826115716190044160000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input160` at Taylor depth ten. -/
def sine160 : IntervalRat :=
  ⟨(325697838220559981465848203636463899047 /
    7446983048826115716190044160000000000000 : ℚ),
   (331517683042548750974294254429054692953 /
    7446983048826115716190044160000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine160_eq :
    IntervalRat.cosComputable input160 10 = cosine160 := by gerver_interval_eq

theorem sine160_eq :
    IntervalRat.sinComputable input160 10 = sine160 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 161. -/
def input161 : IntervalRat :=
  ⟨(57 /
    1280 : ℚ),
   (29 /
    640 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input161` at Taylor depth ten. -/
def cosine161 : IntervalRat :=
  ⟨(294231675562545919986556283601591552931 /
    294533997536579771978219520000000000000 : ℚ),
   (294242012296585163439937131869315469239 /
    294533997536579771978219520000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input161` at Taylor depth ten. -/
def sine161 : IntervalRat :=
  ⟨(1873068455620585157033498434783861453 /
    42076285362368538854031360000000000000 : ℚ),
   (1905951609683864586555441344479498547 /
    42076285362368538854031360000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine161_eq :
    IntervalRat.cosComputable input161 10 = cosine161 := by gerver_interval_eq

theorem sine161_eq :
    IntervalRat.sinComputable input161 10 = sine161 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 162. -/
def input162 : IntervalRat :=
  ⟨(3 /
    64 : ℚ),
   (31 /
    640 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input162` at Taylor depth ten. -/
def cosine162 : IntervalRat :=
  ⟨(294188544230670721721684084439769195169 /
    294533997536579771978219520000000000000 : ℚ),
   (294210476083828696562654633527136404831 /
    294533997536579771978219520000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input162` at Taylor depth ten. -/
def sine162 : IntervalRat :=
  ⟨(13800883031254191755324725897503595169 /
    294533997536579771978219520000000000000 : ℚ),
   (14261266573672213663938652780256404831 /
    294533997536579771978219520000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine162_eq :
    IntervalRat.cosComputable input162 10 = cosine162 := by gerver_interval_eq

theorem sine162_eq :
    IntervalRat.sinComputable input162 10 = sine162 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 163. -/
def input163 : IntervalRat :=
  ⟨(31 /
    640 : ℚ),
   (1 /
    20 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input163` at Taylor depth ten. -/
def cosine163 : IntervalRat :=
  ⟨(305762662086925679713217743 /
    306145268858880000000000000 : ℚ),
   (730625174807097125933115217667 /
    731483095726817280000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input163` at Taylor depth ten. -/
def sine163 : IntervalRat :=
  ⟨(46115170801847955324181561 /
    952451947560960000000000000 : ℚ),
   (495874768238302509565709 /
    9921374453760000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine163_eq :
    IntervalRat.cosComputable input163 10 = cosine163 := by gerver_interval_eq

theorem sine163_eq :
    IntervalRat.sinComputable input163 10 = sine163 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 164. -/
def input164 : IntervalRat :=
  ⟨(2 /
    5 : ℚ),
   (1 /
    2 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input164` at Taylor depth ten. -/
def cosine164 : IntervalRat :=
  ⟨(44791264229263 /
    51093504000000 : ℚ),
   (392422728167171 /
    425779200000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input164` at Taylor depth ten. -/
def sine164 : IntervalRat :=
  ⟨(2176957245143 /
    5677056000000 : ℚ),
   (552755300821 /
    1135411200000 : ℚ),
   by decide +kernel⟩

theorem cosine164_eq :
    IntervalRat.cosComputable input164 10 = cosine164 := by gerver_interval_eq

theorem sine164_eq :
    IntervalRat.sinComputable input164 10 = sine164 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 165. -/
def input165 : IntervalRat :=
  ⟨(1 /
    2 : ℚ),
   (3 /
    5 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input165` at Taylor depth ten. -/
def cosine165 : IntervalRat :=
  ⟨(317126501999383 /
    385000000000000 : ℚ),
   (1353227183655593 /
    1540000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input165` at Taylor depth ten. -/
def sine165 : IntervalRat :=
  ⟨(181093141761883 /
    385000000000000 : ℚ),
   (110773611970621 /
    192500000000000 : ℚ),
   by decide +kernel⟩

theorem cosine165_eq :
    IntervalRat.cosComputable input165 10 = cosine165 := by gerver_interval_eq

theorem sine165_eq :
    IntervalRat.sinComputable input165 10 = sine165 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 166. -/
def input166 : IntervalRat :=
  ⟨(3 /
    5 : ℚ),
   (7 /
    10 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input166` at Taylor depth ten. -/
def cosine166 : IntervalRat :=
  ⟨(434654444092238831 /
    570240000000000000 : ℚ),
   (471738207436864369 /
    570240000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input166` at Taylor depth ten. -/
def sine166 : IntervalRat :=
  ⟨(314699352966772751 /
    570240000000000000 : ℚ),
   (375799701954331249 /
    570240000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine166_eq :
    IntervalRat.cosComputable input166 10 = cosine166 := by gerver_interval_eq

theorem sine166_eq :
    IntervalRat.sinComputable input166 10 = sine166 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 167. -/
def input167 : IntervalRat :=
  ⟨(7 /
    10 : ℚ),
   (4 /
    5 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input167` at Taylor depth ten. -/
def cosine167 : IntervalRat :=
  ⟨(42196614186863 /
    60908203125000 : ℚ),
   (124716558045127 /
    162421875000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input167` at Taylor depth ten. -/
def sine167 : IntervalRat :=
  ⟨(8488369926109 /
    13535156250000 : ℚ),
   (7478848838387 /
    10151367187500 : ℚ),
   by decide +kernel⟩

theorem cosine167_eq :
    IntervalRat.cosComputable input167 10 = cosine167 := by gerver_interval_eq

theorem sine167_eq :
    IntervalRat.sinComputable input167 10 = sine167 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 168. -/
def input168 : IntervalRat :=
  ⟨(0 /
    1 : ℚ),
   (1 /
    20 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input168` at Taylor depth ten. -/
def cosine168 : IntervalRat :=
  ⟨(8164741939199999999999 /
    8174960640000000000000 : ℚ),
   (1 /
    1 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input168` at Taylor depth ten. -/
def sine168 : IntervalRat :=
  ⟨(-1 /
    8174960640000000000000 : ℚ),
   (408748032000000000001 /
    8174960640000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine168_eq :
    IntervalRat.cosComputable input168 10 = cosine168 := by gerver_interval_eq

theorem sine168_eq :
    IntervalRat.sinComputable input168 10 = sine168 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 169. -/
def input169 : IntervalRat :=
  ⟨(1 /
    20 : ℚ),
   (3 /
    40 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input169` at Taylor depth ten. -/
def cosine169 : IntervalRat :=
  ⟨(206114091673420789694453 /
    206695301120000000000000 : ℚ),
   (206437053094036469734027 /
    206695301120000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input169` at Taylor depth ten. -/
def sine169 : IntervalRat :=
  ⟨(10325077424703084029813 /
    206695301120000000000000 : ℚ),
   (2213670024627113435741 /
    29527900160000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine169_eq :
    IntervalRat.cosComputable input169 10 = cosine169 := by gerver_interval_eq

theorem sine169_eq :
    IntervalRat.sinComputable input169 10 = sine169 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 170. -/
def input170 : IntervalRat :=
  ⟨(0 /
    1 : ℚ),
   (1 /
    40 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input170` at Taylor depth ten. -/
def cosine170 : IntervalRat :=
  ⟨(16737087415910399999999999 /
    16742319390720000000000000 : ℚ),
   (1 /
    1 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input170` at Taylor depth ten. -/
def sine170 : IntervalRat :=
  ⟨(-1 /
    16742319390720000000000000 : ℚ),
   (418557984768000000000001 /
    16742319390720000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine170_eq :
    IntervalRat.cosComputable input170 10 = cosine170 := by gerver_interval_eq

theorem sine170_eq :
    IntervalRat.sinComputable input170 10 = sine170 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 171. -/
def input171 : IntervalRat :=
  ⟨(1 /
    40 : ℚ),
   (1 /
    20 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input171` at Taylor depth ten. -/
def cosine171 : IntervalRat :=
  ⟨(32658969885518593979941 /
    32699842560000000000000 : ℚ),
   (6226595426295552377141 /
    6228541440000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input171` at Taylor depth ten. -/
def sine171 : IntervalRat :=
  ⟨(34048143803493600229 /
    1362493440000000000000 : ℚ),
   (136235153134053600917 /
    2724986880000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine171_eq :
    IntervalRat.cosComputable input171 10 = cosine171 := by gerver_interval_eq

theorem sine171_eq :
    IntervalRat.sinComputable input171 10 = sine171 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 172. -/
def input172 : IntervalRat :=
  ⟨(1 /
    40 : ℚ),
   (3 /
    80 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input172` at Taylor depth ten. -/
def cosine172 : IntervalRat :=
  ⟨(423014350961568128941951093 /
    423311976693760000000000000 : ℚ),
   (423179707202867830702025867 /
    423311976693760000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input172` at Taylor depth ten. -/
def sine172 : IntervalRat :=
  ⟨(10580319151238702716925813 /
    423311976693760000000000000 : ℚ),
   (15872545679871416763394187 /
    423311976693760000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine172_eq :
    IntervalRat.cosComputable input172 10 = cosine172 := by gerver_interval_eq

theorem sine172_eq :
    IntervalRat.sinComputable input172 10 = sine172 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 173. -/
def input173 : IntervalRat :=
  ⟨(3 /
    80 : ℚ),
   (1 /
    20 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input173` at Taylor depth ten. -/
def cosine173 : IntervalRat :=
  ⟨(74649080106095638910783 /
    74742497280000000000000 : ℚ),
   (8365274949885818374040929 /
    8371159695360000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input173` at Taylor depth ten. -/
def sine173 : IntervalRat :=
  ⟨(9805865575063853134093 /
    261598740480000000000000 : ℚ),
   (3269217949237112511383 /
    65399685120000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine173_eq :
    IntervalRat.cosComputable input173 10 = cosine173 := by gerver_interval_eq

theorem sine173_eq :
    IntervalRat.sinComputable input173 10 = sine173 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 174. -/
def input174 : IntervalRat :=
  ⟨(0 /
    1 : ℚ),
   (1 /
    160 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input174` at Taylor depth ten. -/
def cosine174 : IntervalRat :=
  ⟨(70221005658969971097599999999999 /
    70222377189774458880000000000000 : ℚ),
   (1 /
    1 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input174` at Taylor depth ten. -/
def sine174 : IntervalRat :=
  ⟨(-1 /
    70222377189774458880000000000000 : ℚ),
   (438889857436090368000000000001 /
    70222377189774458880000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine174_eq :
    IntervalRat.cosComputable input174 10 = cosine174 := by gerver_interval_eq

theorem sine174_eq :
    IntervalRat.sinComputable input174 10 = sine174 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 175. -/
def input175 : IntervalRat :=
  ⟨(1 /
    160 : ℚ),
   (1 /
    80 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input175` at Taylor depth ten. -/
def cosine175 : IntervalRat :=
  ⟨(4285698918726494674947959993 /
    4286033764024320000000000000 : ℚ),
   (45716800570851837149226239983 /
    45717693482926080000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input175` at Taylor depth ten. -/
def sine175 : IntervalRat :=
  ⟨(10204576544713603189029619 /
    1632774767247360000000000000 : ℚ),
   (6803183905359789758172127 /
    544258255749120000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine175_eq :
    IntervalRat.cosComputable input175 10 = cosine175 := by gerver_interval_eq

theorem sine175_eq :
    IntervalRat.sinComputable input175 10 = sine175 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 176. -/
def input176 : IntervalRat :=
  ⟨(401 /
    10240 : ℚ),
   (321 /
    8192 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input176` at Taylor depth ten. -/
def cosine176 : IntervalRat :=
  ⟨(3431678521590981430082767794451734277709204347802143 /
    3434314760573715963796500613987847671920984064000000 : ℚ),
   (85792045150508363424750360166708448878326199885658873 /
    85857869014342899094912515349696191798024601600000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input176` at Taylor depth ten. -/
def sine176 : IntervalRat :=
  ⟨(134453889033120603141029509380760908425910474625567 /
    3434314760573715963796500613987847671920984064000000 : ℚ),
   (26907551210623251100949241476436101245875128240429 /
    686862952114743192759300122797569534384196812800000 : ℚ),
   by decide +kernel⟩

theorem cosine176_eq :
    IntervalRat.cosComputable input176 10 = cosine176 := by gerver_interval_eq

theorem sine176_eq :
    IntervalRat.sinComputable input176 10 = sine176 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 177. -/
def input177 : IntervalRat :=
  ⟨(321 /
    8192 : ℚ),
   (803 /
    20480 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input177` at Taylor depth ten. -/
def cosine177 : IntervalRat :=
  ⟨(963959066607327534460464839642858300480932656535217423 /
    964700510220860543918667012069062879477760000000000000 : ℚ),
   (963959989779967926704503185423581937702334781580582577 /
    964700510220860543918667012069062879477760000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input177` at Taylor depth ten. -/
def sine177 : IntervalRat :=
  ⟨(37791690094434461355381730108488907273831074014417423 /
    964700510220860543918667012069062879477760000000000000 : ℚ),
   (37815248384346196761666578694315231681013577505582577 /
    964700510220860543918667012069062879477760000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine177_eq :
    IntervalRat.cosComputable input177 10 = cosine177 := by gerver_interval_eq

theorem sine177_eq :
    IntervalRat.sinComputable input177 10 = sine177 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 178. -/
def input178 : IntervalRat :=
  ⟨(201 /
    5120 : ℚ),
   (1609 /
    40960 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input178` at Taylor depth ten. -/
def cosine178 : IntervalRat :=
  ⟨(21716007399128005329440384198249786669399407493202507982631 /
    21732773094255546333399730447891848548874977280000000000000 : ℚ),
   (21716028235222475972749236822041845939382651645245641726169 /
    21732773094255546333399730447891848548874977280000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input178` at Taylor depth ten. -/
def sine178 : IntervalRat :=
  ⟨(852961725129259130481874048504810420530120031631935530791 /
    21732773094255546333399730447891848548874977280000000000000 : ℚ),
   (853492446792688267315711663205415000875209853026596821209 /
    21732773094255546333399730447891848548874977280000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine178_eq :
    IntervalRat.cosComputable input178 10 = cosine178 := by gerver_interval_eq

theorem sine178_eq :
    IntervalRat.sinComputable input178 10 = sine178 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 179. -/
def input179 : IntervalRat :=
  ⟨(1609 /
    40960 : ℚ),
   (161 /
    4096 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input179` at Taylor depth ten. -/
def cosine179 : IntervalRat :=
  ⟨(19389273710214156338526413529115302202534283414297 /
    19404261691299594940535473614189150490066944000000 : ℚ),
   (161577436045298127779232641384215645683574936080581 /
    161702180760829957837795613451576254083891200000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input179` at Taylor depth ten. -/
def sine179 : IntervalRat :=
  ⟨(84671815576031308672079148971804947925097769873 /
    2156029076811066104503941512687683387785216000000 : ℚ),
   (50834679930920725113042183723080048316026090153 /
    1293617446086639662702364907612610032671129600000 : ℚ),
   by decide +kernel⟩

theorem cosine179_eq :
    IntervalRat.cosComputable input179 10 = cosine179 := by gerver_interval_eq

theorem sine179_eq :
    IntervalRat.sinComputable input179 10 = sine179 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 180. -/
def input180 : IntervalRat :=
  ⟨(161 /
    4096 : ℚ),
   (1611 /
    40960 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input180` at Taylor depth ten. -/
def cosine180 : IntervalRat :=
  ⟨(268098341960592123559748067816124625953091873303134530269 /
    268305840669821559671601610467800599368826880000000000000 : ℚ),
   (268098599516171826109324759473482085129843071083527869731 /
    268305840669821559671601610467800599368826880000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input180` at Taylor depth ten. -/
def sine180 : IntervalRat :=
  ⟨(10543482424377781923882818491001276075082170219512130269 /
    268305840669821559671601610467800599368826880000000000000 : ℚ),
   (10550034547869405513942887193463459332715014538247869731 /
    268305840669821559671601610467800599368826880000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine180_eq :
    IntervalRat.cosComputable input180 10 = cosine180 := by gerver_interval_eq

theorem sine180_eq :
    IntervalRat.sinComputable input180 10 = sine180 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 181. -/
def input181 : IntervalRat :=
  ⟨(1611 /
    40960 : ℚ),
   (403 /
    10240 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input181` at Taylor depth ten. -/
def cosine181 : IntervalRat :=
  ⟨(5177484710033497449081005123100613053886363689008093 /
    5181496881069075187063152896855318200320000000000000 : ℚ),
   (10354979374021547805972281189689082393995320393897239 /
    10362993762138150374126305793710636400640000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input181` at Taylor depth ten. -/
def sine181 : IntervalRat :=
  ⟨(203741133507146204594587271388603727262782181191253 /
    5181496881069075187063152896855318200320000000000000 : ℚ),
   (203867667533453286252352289313320112873763316920747 /
    5181496881069075187063152896855318200320000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine181_eq :
    IntervalRat.cosComputable input181 10 = cosine181 := by gerver_interval_eq

theorem sine181_eq :
    IntervalRat.sinComputable input181 10 = sine181 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 182. -/
def input182 : IntervalRat :=
  ⟨(1 /
    10 : ℚ),
   (1 /
    8 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input182` at Taylor depth ten. -/
def cosine182 : IntervalRat :=
  ⟨(212628850728893130127 /
    214301688201216000000 : ℚ),
   (1776929787404648333059 /
    1785847401676800000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input182` at Taylor depth ten. -/
def sine182 : IntervalRat :=
  ⟨(7124796327435129989 /
    71433896067072000000 : ℚ),
   (1782873314109281663 /
    14286779213414400000 : ℚ),
   by decide +kernel⟩

theorem cosine182_eq :
    IntervalRat.cosComputable input182 10 = cosine182 := by gerver_interval_eq

theorem sine182_eq :
    IntervalRat.sinComputable input182 10 = sine182 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 183. -/
def input183 : IntervalRat :=
  ⟨(1 /
    8 : ℚ),
   (3 /
    20 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input183` at Taylor depth ten. -/
def cosine183 : IntervalRat :=
  ⟨(399166024366037181877 /
    403701760000000000000 : ℚ),
   (1602215002084949175617 /
    1614807040000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input183` at Taylor depth ten. -/
def sine183 : IntervalRat :=
  ⟨(392762754381384209 /
    3153920000000000000 : ℚ),
   (15099436335505158437 /
    100925440000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine183_eq :
    IntervalRat.cosComputable input183 10 = cosine183 := by gerver_interval_eq

theorem sine183_eq :
    IntervalRat.sinComputable input183 10 = sine183 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 184. -/
def input184 : IntervalRat :=
  ⟨(1 /
    5 : ℚ),
   (1 /
    4 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input184` at Taylor depth ten. -/
def cosine184 : IntervalRat :=
  ⟨(1251609743104991 /
    1291845632000000 : ℚ),
   (2563939792465755401 /
    2615987404800000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input184` at Taylor depth ten. -/
def sine184 : IntervalRat :=
  ⟨(6903445212484741 /
    34879832064000000 : ℚ),
   (1732401291097471 /
    6975966412800000 : ℚ),
   by decide +kernel⟩

theorem cosine184_eq :
    IntervalRat.cosComputable input184 10 = cosine184 := by gerver_interval_eq

theorem sine184_eq :
    IntervalRat.sinComputable input184 10 = sine184 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 185. -/
def input185 : IntervalRat :=
  ⟨(1 /
    4 : ℚ),
   (3 /
    10 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input185` at Taylor depth ten. -/
def cosine185 : IntervalRat :=
  ⟨(376591323109048129 /
    394240000000000000 : ℚ),
   (1528048831236710609 /
    1576960000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input185` at Taylor depth ten. -/
def sine185 : IntervalRat :=
  ⟨(48543105054288127 /
    197120000000000000 : ℚ),
   (29261383940082499 /
    98560000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine185_eq :
    IntervalRat.cosComputable input185 10 = cosine185 := by gerver_interval_eq

theorem sine185_eq :
    IntervalRat.sinComputable input185 10 = sine185 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 186. -/
def input186 : IntervalRat :=
  ⟨(321 /
    8192 : ℚ),
   (6421 /
    163840 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input186` at Taylor depth ten. -/
def cosine186 : IntervalRat :=
  ⟨(91083864065906825827479365252899809383062399387985223920718907379 /
    91153857120328415008363823016514571935940512705413120000000000000 : ℚ),
   (13011983695470407389034090514074604786694312773728542831663241803 /
    13021979588618345001194831859502081705134358957916160000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input186` at Taylor depth ten. -/
def sine186 : IntervalRat :=
  ⟨(3570910460873231023876887612671542876775214603017358742197307379 /
    91153857120328415008363823016514571935940512705413120000000000000 : ℚ),
   (3571466962272653630733924980863215748398161550512475794762692621 /
    91153857120328415008363823016514571935940512705413120000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine186_eq :
    IntervalRat.cosComputable input186 10 = cosine186 := by gerver_interval_eq

theorem sine186_eq :
    IntervalRat.sinComputable input186 10 = sine186 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 187. -/
def input187 : IntervalRat :=
  ⟨(6421 /
    163840 : ℚ),
   (3211 /
    81920 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input187` at Taylor depth ten. -/
def cosine187 : IntervalRat :=
  ⟨(44474532356301895860013131723758340293468556771581009115553069 /
    44508719297035358890802647957282505828095953469440000000000000 : ℚ),
   (14824847667885425541064810591036254614521972211519129620436977 /
    14836239765678452963600882652427501942698651156480000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input187` at Taylor depth ten. -/
def sine187 : IntervalRat :=
  ⟨(581293358176851566709008340967146536469854107948918921442063 /
    14836239765678452963600882652427501942698651156480000000000000 : ℚ),
   (83054847797674059905773660519409283471578569404380363889991 /
    2119462823668350423371554664632500277528378736640000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine187_eq :
    IntervalRat.cosComputable input187 10 = cosine187 := by gerver_interval_eq

theorem sine187_eq :
    IntervalRat.sinComputable input187 10 = sine187 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 188. -/
def input188 : IntervalRat :=
  ⟨(3211 /
    81920 : ℚ),
   (6423 /
    163840 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input188` at Taylor depth ten. -/
def cosine188 : IntervalRat :=
  ⟨(1124491610643365452710298289350326158189175471086730956420874473 /
    1125356260744795247016837321191537925135068058091520000000000000 : ℚ),
   (160641697127495801375370059076631257490599822609041702889202801 /
    160765180106399321002405331598791132162152579727360000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input188` at Taylor depth ten. -/
def sine188 : IntervalRat :=
  ⟨(44099041040380984138711764138616875230098335145102964652441833 /
    1125356260744795247016837321191537925135068058091520000000000000 : ℚ),
   (44105911429123751918024273318633717072387964993900947211878167 /
    1125356260744795247016837321191537925135068058091520000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine188_eq :
    IntervalRat.cosComputable input188 10 = cosine188 := by gerver_interval_eq

theorem sine188_eq :
    IntervalRat.sinComputable input188 10 = sine188 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 189. -/
def input189 : IntervalRat :=
  ⟨(6423 /
    163840 : ℚ),
   (803 /
    20480 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input189` at Taylor depth ten. -/
def cosine189 : IntervalRat :=
  ⟨(481979533348009114557671135642382751330517633200330489 /
    482350255110430271959333506034531439738880000000000000 : ℚ),
   (61693395042757450926046778455701520296837300735140685883 /
    61740832654135074810794688772420024286576640000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input189` at Taylor depth ten. -/
def sine189 : IntervalRat :=
  ⟨(37809349763398285002012891815761847383444391721041423 /
    964700510220860543918667012069062879477760000000000000 : ℚ),
   (37815239336580871302378242782050988822038547605294577 /
    964700510220860543918667012069062879477760000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine189_eq :
    IntervalRat.cosComputable input189 10 = cosine189 := by gerver_interval_eq

theorem sine189_eq :
    IntervalRat.sinComputable input189 10 = sine189 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 190. -/
def input190 : IntervalRat :=
  ⟨(401 /
    10240 : ℚ),
   (3209 /
    81920 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input190` at Taylor depth ten. -/
def cosine190 : IntervalRat :=
  ⟨(705945633706624859038903110523504619795589830237033682374617 /
    706487607889450141123851554877500092509459578880000000000000 : ℚ),
   (44474596203303416139932019710086939478855242110166883990968729 /
    44508719297035358890802647957282505828095953469440000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input190` at Taylor depth ten. -/
def sine190 : IntervalRat :=
  ⟨(82977270462274318134809550488512967797946301874329794981771 /
    2119462823668350423371554664632500277528378736640000000000000 : ℚ),
   (581022045984679592666988406316251503508393150047174585463603 /
    14836239765678452963600882652427501942698651156480000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine190_eq :
    IntervalRat.cosComputable input190 10 = cosine190 := by gerver_interval_eq

theorem sine190_eq :
    IntervalRat.sinComputable input190 10 = sine190 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 191. -/
def input191 : IntervalRat :=
  ⟨(3209 /
    81920 : ℚ),
   (321 /
    8192 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input191` at Taylor depth ten. -/
def cosine191 : IntervalRat :=
  ⟨(3431678521801063485246857552929558101315826956229663 /
    3434314760573715963796500613987847671920984064000000 : ℚ),
   (85792004106790410906529616757578220593769942042117497 /
    85857869014342899094912515349696191798024601600000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input191` at Taylor depth ten. -/
def sine191 : IntervalRat :=
  ⟨(134495801094938928465570001782349399583722298790431 /
    3434314760573715963796500613987847671920984064000000 : ℚ),
   (26907546921655880610390882919902154694746530777389 /
    686862952114743192759300122797569534384196812800000 : ℚ),
   by decide +kernel⟩

theorem cosine191_eq :
    IntervalRat.cosComputable input191 10 = cosine191 := by gerver_interval_eq

theorem sine191_eq :
    IntervalRat.sinComputable input191 10 = sine191 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 192. -/
def input192 : IntervalRat :=
  ⟨(803 /
    20480 : ℚ),
   (1285 /
    32768 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input192` at Taylor depth ten. -/
def cosine192 : IntervalRat :=
  ⟨(373079149956078915494092354783387976680949568909444073991 /
    373366198764865187874258219075643686649612340041372139520 : ℚ),
   (1727218700529111011615656358257609636276273482876039600911 /
    1728547216504005499417862125350202253007464537228574720000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input192` at Taylor depth ten. -/
def sine192 : IntervalRat :=
  ⟨(24392596050849521089839213000925298081322627034110589793 /
    622276997941441979790430365126072811082687233402286899200 : ℚ),
   (8132131700538239969681509063749369027715810450912717877 /
    207425665980480659930143455042024270360895744467428966400 : ℚ),
   by decide +kernel⟩

theorem cosine192_eq :
    IntervalRat.cosComputable input192 10 = cosine192 := by gerver_interval_eq

theorem sine192_eq :
    IntervalRat.sinComputable input192 10 = sine192 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 193. -/
def input193 : IntervalRat :=
  ⟨(1285 /
    32768 : ℚ),
   (3213 /
    81920 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input193` at Taylor depth ten. -/
def cosine193 : IntervalRat :=
  ⟨(78438253547120207578164056062466577507978218420762827042189 /
    78498623098827793458205728319722232501051064320000000000000 : ℚ),
   (78438272337220202267035908606828116917088038831540672957811 /
    78498623098827793458205728319722232501051064320000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input193` at Taylor depth ten. -/
def sine193 : IntervalRat :=
  ⟨(3077541231234443727140837486233575248660451792996827042189 /
    78498623098827793458205728319722232501051064320000000000000 : ℚ),
   (3078020471635306619044480696689166340420774651803172957811 /
    78498623098827793458205728319722232501051064320000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine193_eq :
    IntervalRat.cosComputable input193 10 = cosine193 := by gerver_interval_eq

theorem sine193_eq :
    IntervalRat.sinComputable input193 10 = sine193 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 194. -/
def input194 : IntervalRat :=
  ⟨(3213 /
    81920 : ℚ),
   (1607 /
    40960 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input194` at Taylor depth ten. -/
def cosine194 : IntervalRat :=
  ⟨(21716049049007429658300489649222574853588408153933085928617 /
    21732773094255546333399730447891848548874977280000000000000 : ℚ),
   (21716059455720140179057957429117802244595485326083747853783 /
    21732773094255546333399730447891848548874977280000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input194` at Taylor depth ten. -/
def sine194 : IntervalRat :=
  ⟨(852166596446426185491636631292982742093743952231054514857 /
    21732773094255546333399730447891848548874977280000000000000 : ℚ),
   (852431957129834563668885869771631908736082989872399181143 /
    21732773094255546333399730447891848548874977280000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine194_eq :
    IntervalRat.cosComputable input194 10 = cosine194 := by gerver_interval_eq

theorem sine194_eq :
    IntervalRat.sinComputable input194 10 = sine194 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 195. -/
def input195 : IntervalRat :=
  ⟨(803 /
    20480 : ℚ),
   (3213 /
    81920 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input195` at Taylor depth ten. -/
def cosine195 : IntervalRat :=
  ⟨(78438253544711968811396541635137733045160969585927012913549 /
    78498623098827793458205728319722232501051064320000000000000 : ℚ),
   (78438291121987656502337062741991059841451516987862500077171 /
    78498623098827793458205728319722232501051064320000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input195` at Taylor depth ten. -/
def sine195 : IntervalRat :=
  ⟨(3077062236471397528326669887061704769417797965425704866189 /
    78498623098827793458205728319722232501051064320000000000000 : ℚ),
   (3078020717234885901212506004638913470809852877073776733811 /
    78498623098827793458205728319722232501051064320000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine195_eq :
    IntervalRat.cosComputable input195 10 = cosine195 := by gerver_interval_eq

theorem sine195_eq :
    IntervalRat.sinComputable input195 10 = sine195 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 196. -/
def input196 : IntervalRat :=
  ⟨(3211 /
    81920 : ℚ),
   (803 /
    20480 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input196` at Taylor depth ten. -/
def cosine196 : IntervalRat :=
  ⟨(107106562962938895598819141321209559087708850186607367 /
    107188945580095615990963001341006986608640000000000000 : ℚ),
   (240989882081161511975482077847198619761878488953613093 /
    241175127555215135979666753017265719869440000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input196` at Taylor depth ten. -/
def sine196 : IntervalRat :=
  ⟨(12601154402358967394577501410900485027607761285531141 /
    321566836740286847972889004023020959825920000000000000 : ℚ),
   (12605080784324102158005773433780426607330625805924859 /
    321566836740286847972889004023020959825920000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine196_eq :
    IntervalRat.cosComputable input196 10 = cosine196 := by gerver_interval_eq

theorem sine196_eq :
    IntervalRat.sinComputable input196 10 = sine196 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 197. -/
def input197 : IntervalRat :=
  ⟨(321 /
    8192 : ℚ),
   (3211 /
    81920 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input197` at Taylor depth ten. -/
def cosine197 : IntervalRat :=
  ⟨(44474532354938972903448810572853812770771709895201476151974189 /
    44508719297035358890802647957282505828095953469440000000000000 : ℚ),
   (44474553647989655373529531899841241031147972714608545428825811 /
    44508719297035358890802647957282505828095953469440000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input197` at Taylor depth ten. -/
def sine197 : IntervalRat :=
  ⟨(1743608484413265342387086370911585735204378577336332651174189 /
    44508719297035358890802647957282505828095953469440000000000000 : ℚ),
   (1744151942832799345887373421740562616581730115064368788825811 /
    44508719297035358890802647957282505828095953469440000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine197_eq :
    IntervalRat.cosComputable input197 10 = cosine197 := by gerver_interval_eq

theorem sine197_eq :
    IntervalRat.sinComputable input197 10 = sine197 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 198. -/
def input198 : IntervalRat :=
  ⟨(1607 /
    40960 : ℚ),
   (643 /
    16384 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input198` at Taylor depth ten. -/
def cosine198 : IntervalRat :=
  ⟨(63252547041074534033047136723192416742530888168950347341 /
    63301289666894732644697099317024008288847578267648000000 : ℚ),
   (14231829906507353316645465389108080343302793639857519216211 /
    14242790175051314845056847346330401864990705110220800000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input198` at Taylor depth ten. -/
def sine198 : IntervalRat :=
  ⟨(1064094531477433697434018002796247490733100376666918433 /
    27129124142954885419155899707296003552363247828992000000 : ℚ),
   (70961718835668702226797637344230477170309660333695281 /
    1808608276196992361277059980486400236824216521932800000 : ℚ),
   by decide +kernel⟩

theorem cosine198_eq :
    IntervalRat.cosComputable input198 10 = cosine198 := by gerver_interval_eq

theorem sine198_eq :
    IntervalRat.sinComputable input198 10 = sine198 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 199. -/
def input199 : IntervalRat :=
  ⟨(643 /
    16384 : ℚ),
   (201 /
    5120 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input199` at Taylor depth ten. -/
def cosine199 : IntervalRat :=
  ⟨(285356293794881931686483967502416565551214663183 /
    285576327219415519569177298107105280000000000000 : ℚ),
   (511358723685155731842018179836568613036402713541689 /
    511752778377192611067965718207932661760000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input199` at Taylor depth ten. -/
def sine199 : IntervalRat :=
  ⟨(175074019893053573247167220501524415113917247 /
    4462130112803367493268395282923520000000000000 : ℚ),
   (1225899522698572631850649126315788989380860521 /
    31234910789623572452878766980464640000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine199_eq :
    IntervalRat.cosComputable input199 10 = cosine199 := by gerver_interval_eq

theorem sine199_eq :
    IntervalRat.sinComputable input199 10 = sine199 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 200. -/
def input200 : IntervalRat :=
  ⟨(3209 /
    81920 : ℚ),
   (6419 /
    163840 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input200` at Taylor depth ten. -/
def cosine200 : IntervalRat :=
  ⟨(13011986808018356422131424855108937221971087908804119651539114563 /
    13021979588618345001194831859502081705134358957916160000000000000 : ℚ),
   (4337329973891572811257858128975306149025723219597304447149750079 /
    4340659862872781667064943953167360568378119652638720000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input200` at Taylor depth ten. -/
def sine200 : IntervalRat :=
  ⟨(169990409378259043923134901846231026121492451547179135742036161 /
    4340659862872781667064943953167360568378119652638720000000000000 : ℚ),
   (170016909440673742540861876687936620699156375791173138698155839 /
    4340659862872781667064943953167360568378119652638720000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine200_eq :
    IntervalRat.cosComputable input200 10 = cosine200 := by gerver_interval_eq

theorem sine200_eq :
    IntervalRat.sinComputable input200 10 = sine200 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 201. -/
def input201 : IntervalRat :=
  ⟨(6419 /
    163840 : ℚ),
   (321 /
    8192 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input201` at Taylor depth ten. -/
def cosine201 : IntervalRat :=
  ⟨(3431678521906129066598928452438559782364780015122623 /
    3434314760573715963796500613987847671920984064000000 : ℚ),
   (85791983580134366037426808777977368000770069405289843 /
    85857869014342899094912515349696191798024601600000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input201` at Taylor depth ten. -/
def sine201 : IntervalRat :=
  ⟨(134516757125848668203822633529061222462474705162783 /
    3434314760573715963796500613987847671920984064000000 : ℚ),
   (26907544776670913525629123585626196028536132077869 /
    686862952114743192759300122797569534384196812800000 : ℚ),
   by decide +kernel⟩

theorem cosine201_eq :
    IntervalRat.cosComputable input201 10 = cosine201 := by gerver_interval_eq

theorem sine201_eq :
    IntervalRat.sinComputable input201 10 = sine201 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 202. -/
def input202 : IntervalRat :=
  ⟨(103 /
    2560 : ℚ),
   (207 /
    5120 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input202` at Taylor depth ten. -/
def cosine202 : IntervalRat :=
  ⟨(4458483795856475428273771096191350244284515831 /
    4462130112803367493268395282923520000000000000 : ℚ),
   (31209632619317069690618708213111213818358289983 /
    31234910789623572452878766980464640000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input202` at Taylor depth ten. -/
def sine202 : IntervalRat :=
  ⟨(1256374778334101913285820374829557499221813697 /
    31234910789623572452878766980464640000000000000 : ℚ),
   (1262477000910616200720540136298231554451658303 /
    31234910789623572452878766980464640000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine202_eq :
    IntervalRat.cosComputable input202 10 = cosine202 := by gerver_interval_eq

theorem sine202_eq :
    IntervalRat.sinComputable input202 10 = sine202 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 203. -/
def input203 : IntervalRat :=
  ⟨(207 /
    5120 : ℚ),
   (13 /
    320 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input203` at Taylor depth ten. -/
def cosine203 : IntervalRat :=
  ⟨(147145491283500171492701954649185295617 /
    147266998768289885989109760000000000000 : ℚ),
   (37669544185592385757137492907157234013433 /
    37700351684682210813212098560000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input203` at Taylor depth ten. -/
def sine203 : IntervalRat :=
  ⟨(744040143353353616131527295816137889 /
    18408374846036235748638720000000000000 : ℚ),
   (46727282084800290931346067892280171 /
    1150523427877264734289920000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine203_eq :
    IntervalRat.cosComputable input203 10 = cosine203 := by gerver_interval_eq

theorem sine203_eq :
    IntervalRat.sinComputable input203 10 = sine203 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 204. -/
def input204 : IntervalRat :=
  ⟨(801 /
    20480 : ℚ),
   (641 /
    16384 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input204` at Taylor depth ten. -/
def cosine204 : IntervalRat :=
  ⟨(569275647758686348512229506521453045576298565995461679631 /
    569711607002052593802273893853216074599628204408832000000 : ℚ),
   (14231897995009329952653004933974099753692974789373202822281 /
    14242790175051314845056847346330401864990705110220800000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input204` at Taylor depth ten. -/
def sine204 : IntervalRat :=
  ⟨(22276493659915229474216110765101529587459161186910673423 /
    569711607002052593802273893853216074599628204408832000000 : ℚ),
   (4456689984207277004087345287134981545627423964716740093 /
    113942321400410518760454778770643214919925640881766400000 : ℚ),
   by decide +kernel⟩

theorem cosine204_eq :
    IntervalRat.cosComputable input204 10 = cosine204 := by gerver_interval_eq

theorem sine204_eq :
    IntervalRat.sinComputable input204 10 = sine204 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 205. -/
def input205 : IntervalRat :=
  ⟨(641 /
    16384 : ℚ),
   (1603 /
    40960 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input205` at Taylor depth ten. -/
def cosine205 : IntervalRat :=
  ⟨(344700510964477348260543447172863964083009648625193329531 /
    344964652289770576720630642030029342045634560000000000000 : ℚ),
   (3102306081652471172577860269006915312270391595093390834221 /
    3104681870607935190485675778270264078410711040000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input205` at Taylor depth ten. -/
def sine205 : IntervalRat :=
  ⟨(40478375434846543828196510705945620329363802474426388593 /
    1034893956869311730161891926090088026136903680000000000000 : ℚ),
   (13497003880584053276862328124503928274326844609217870469 /
    344964652289770576720630642030029342045634560000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine205_eq :
    IntervalRat.cosComputable input205 10 = cosine205 := by gerver_interval_eq

theorem sine205_eq :
    IntervalRat.sinComputable input205 10 = sine205 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 206. -/
def input206 : IntervalRat :=
  ⟨(1603 /
    40960 : ℚ),
   (3207 /
    81920 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input206` at Taylor depth ten. -/
def cosine206 : IntervalRat :=
  ⟨(549069351426998032039164682724821926579865361550245129390617 /
    549490361691794554207440098238055627507357450240000000000000 : ℚ),
   (549069613976645162557219745514697715804962422471374200862183 /
    549490361691794554207440098238055627507357450240000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input206` at Taylor depth ten. -/
def sine206 : IntervalRat :=
  ⟨(21499220666215007456953295423008108253317499412783248476697 /
    549490361691794554207440098238055627507357450240000000000000 : ℚ),
   (21505930025142540646747603449059445066868103272679656355303 /
    549490361691794554207440098238055627507357450240000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine206_eq :
    IntervalRat.cosComputable input206 10 = cosine206 := by gerver_interval_eq

theorem sine206_eq :
    IntervalRat.sinComputable input206 10 = sine206 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 207. -/
def input207 : IntervalRat :=
  ⟨(3207 /
    81920 : ℚ),
   (401 /
    10240 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input207` at Taylor depth ten. -/
def cosine207 : IntervalRat :=
  ⟨(10355048858995018476803198922907094867185263399375143 /
    10362993762138150374126305793710636400640000000000000 : ℚ),
   (662723443970374071313027672401554248438898857108468633 /
    663231600776841623944083570797480729640960000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input207` at Taylor depth ten. -/
def sine207 : IntervalRat :=
  ⟨(28970448050205641441498139535570849071732093265657 /
    740213840152725026723307556693616885760000000000000 : ℚ),
   (28979486172571335719747438666359227000677116174343 /
    740213840152725026723307556693616885760000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine207_eq :
    IntervalRat.cosComputable input207 10 = cosine207 := by gerver_interval_eq

theorem sine207_eq :
    IntervalRat.sinComputable input207 10 = sine207 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 208. -/
def input208 : IntervalRat :=
  ⟨(1601 /
    40960 : ℚ),
   (3203 /
    81920 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input208` at Taylor depth ten. -/
def cosine208 : IntervalRat :=
  ⟨(4941633607799881325465890995878571518848912748456749834205597 /
    4945413255226150987866960884142500647566217052160000000000000 : ℚ),
   (44474723710191084607352875513649794482988830384047647307839867 /
    44508719297035358890802647957282505828095953469440000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input208` at Taylor depth ten. -/
def sine208 : IntervalRat :=
  ⟨(579755086453597656056302931088472568489629659735431697755351 /
    14836239765678452963600882652427501942698651156480000000000000 : ℚ),
   (579936239029317110434142566625469032667684010980726418084649 /
    14836239765678452963600882652427501942698651156480000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine208_eq :
    IntervalRat.cosComputable input208 10 = cosine208 := by gerver_interval_eq

theorem sine208_eq :
    IntervalRat.sinComputable input208 10 = sine208 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 209. -/
def input209 : IntervalRat :=
  ⟨(3203 /
    81920 : ℚ),
   (801 /
    20480 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input209` at Taylor depth ten. -/
def cosine209 : IntervalRat :=
  ⟨(130908522279135310252957853671689646393390515866287999 /
    131008711264561308433399223861230761410560000000000000 : ℚ),
   (65454292408641831545711727054526294669273650476703313 /
    65504355632280654216699611930615380705280000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input209` at Taylor depth ten. -/
def sine209 : IntervalRat :=
  ⟨(5121019632435103816993425754020132245442629482288879 /
    131008711264561308433399223861230761410560000000000000 : ℚ),
   (5122619267493409170048110428452673351223780612303121 /
    131008711264561308433399223861230761410560000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine209_eq :
    IntervalRat.cosComputable input209 10 = cosine209 := by gerver_interval_eq

theorem sine209_eq :
    IntervalRat.sinComputable input209 10 = sine209 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 210. -/
def input210 : IntervalRat :=
  ⟨(321 /
    8192 : ℚ),
   (12841 /
    327680 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input210` at Taylor depth ten. -/
def cosine210 : IntervalRat :=
  ⟨(186539775930633192857423537616050300847983933632998588540996617690759 /
    186683099382432593937129109537821843324806170020686069760000000000000 : ℚ),
   (186539798255407172422442586699340997602896994137562711663306537509241 /
    186683099382432593937129109537821843324806170020686069760000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input210` at Taylor depth ten. -/
def sine210 : IntervalRat :=
  ⟨(7313224915464256505555010297952064211608140524480599738554582490759 /
    186683099382432593937129109537821843324806170020686069760000000000000 : ℚ),
   (7313794772885908986265125694692991137875873981779798435817257509241 /
    186683099382432593937129109537821843324806170020686069760000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine210_eq :
    IntervalRat.cosComputable input210 10 = cosine210 := by gerver_interval_eq

theorem sine210_eq :
    IntervalRat.sinComputable input210 10 = sine210 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 211. -/
def input211 : IntervalRat :=
  ⟨(12841 /
    327680 : ℚ),
   (6421 /
    163840 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input211` at Taylor depth ten. -/
def cosine211 : IntervalRat :=
  ⟨(4337326860347712858280722215916458619086674535932725204367952359 /
    4340659862872781667064943953167360568378119652638720000000000000 : ℚ),
   (91083874968919451210177470547533729486387421268683226462826613261 /
    91153857120328415008363823016514571935940512705413120000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input211` at Taylor depth ten. -/
def sine211 : IntervalRat :=
  ⟨(44088747767598900342369920584770977144281262526017256720422659 /
    1125356260744795247016837321191537925135068058091520000000000000 : ℚ),
   (1190488939960256049341849411576409857935603616223791491818476207 /
    30384619040109471669454607672171523978646837568471040000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine211_eq :
    IntervalRat.cosComputable input211 10 = cosine211 := by gerver_interval_eq

theorem sine211_eq :
    IntervalRat.sinComputable input211 10 = sine211 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 212. -/
def input212 : IntervalRat :=
  ⟨(401 /
    10240 : ℚ),
   (12833 /
    327680 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input212` at Taylor depth ten. -/
def cosine212 : IntervalRat :=
  ⟨(62179984811493634688362616511033845879157149183059342625134442861621 /
    62227699794144197979043036512607281108268723340228689920000000000000 : ℚ),
   (186539976745345908394848204254969319512762899489765204662005460960097 /
    186683099382432593937129109537821843324806170020686069760000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input212` at Taylor depth ten. -/
def sine212 : IntervalRat :=
  ⟨(90230502708087725376973431829319068310454666297286477553477378543 /
    2304729622005340665890482833800269670676619382971432960000000000000 : ℚ),
   (2436413525531702494730713916485237025742491001962772286434304699339 /
    62227699794144197979043036512607281108268723340228689920000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine212_eq :
    IntervalRat.cosComputable input212 10 = cosine212 := by gerver_interval_eq

theorem sine212_eq :
    IntervalRat.sinComputable input212 10 = sine212 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 213. -/
def input213 : IntervalRat :=
  ⟨(12833 /
    327680 : ℚ),
   (6417 /
    163840 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input213` at Taylor depth ten. -/
def cosine213 : IntervalRat :=
  ⟨(1124493225113211617587739653208527470528236500604709967015455647 /
    1125356260744795247016837321191537925135068058091520000000000000 : ℚ),
   (1124493359617236177737392941620786642081636374339500116637421153 /
    1125356260744795247016837321191537925135068058091520000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input213` at Taylor depth ten. -/
def sine213 : IntervalRat :=
  ⟨(44061294331760303356677880408388867590153888640276920866530207 /
    1125356260744795247016837321191537925135068058091520000000000000 : ℚ),
   (44064729524557262025494541152970928214754607883758208215325793 /
    1125356260744795247016837321191537925135068058091520000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine213_eq :
    IntervalRat.cosComputable input213 10 = cosine213 := by gerver_interval_eq

theorem sine213_eq :
    IntervalRat.sinComputable input213 10 = sine213 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 214. -/
def input214 : IntervalRat :=
  ⟨(6417 /
    163840 : ℚ),
   (2567 /
    65536 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input214` at Taylor depth ten. -/
def cosine214 : IntervalRat :=
  ⟨(341101549383209517657991590756653059456033655715564425561814943 /
    341363381727876743199321800297731370651074139466397384704000000 : ℚ),
   (59692778282651184994458519628597260497990412485753390425609239119 /
    59738591802378430059881315052102989863937974406619542323200000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input214` at Taylor depth ten. -/
def sine214 : IntervalRat :=
  ⟨(93565558640523833734553653708034888438930591462784819631818073 /
    2389543672095137202395252602084119594557518976264781692928000000 : ℚ),
   (18714570562755400475114382011110790505215657178255565868747707 /
    477908734419027440479050520416823918911503795252956338585600000 : ℚ),
   by decide +kernel⟩

theorem cosine214_eq :
    IntervalRat.cosComputable input214 10 = cosine214 := by gerver_interval_eq

theorem sine214_eq :
    IntervalRat.sinComputable input214 10 = sine214 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 215. -/
def input215 : IntervalRat :=
  ⟨(2567 /
    65536 : ℚ),
   (3209 /
    81920 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input215` at Taylor depth ten. -/
def cosine215 : IntervalRat :=
  ⟨(14824858308519337393864211843988190998715830068079991643008397 /
    14836239765678452963600882652427501942698651156480000000000000 : ℚ),
   (44474580246126304332769439280625891433796640789307406948337309 /
    44508719297035358890802647957282505828095953469440000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input215` at Taylor depth ten. -/
def sine215 : IntervalRat :=
  ⟨(193658896112619886811291066451785477838909491421657564802799 /
    4945413255226150987866960884142500647566217052160000000000000 : ℚ),
   (581021976527756203454924273265169738379762019135173225591603 /
    14836239765678452963600882652427501942698651156480000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine215_eq :
    IntervalRat.cosComputable input215 10 = cosine215 := by gerver_interval_eq

theorem sine215_eq :
    IntervalRat.sinComputable input215 10 = sine215 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 216. -/
def input216 : IntervalRat :=
  ⟨(3209 /
    81920 : ℚ),
   (12837 /
    327680 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input216` at Taylor depth ten. -/
def cosine216 : IntervalRat :=
  ⟨(209360118065606455998242554152843547210019492310588983519747029337 /
    209520874727758242353680257618206333697874489361039360000000000000 : ℚ),
   (209360143113664247184828344193560312273355041661852396529430775463 /
    209520874727758242353680257618206333697874489361039360000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input216` at Taylor depth ten. -/
def sine216 : IntervalRat :=
  ⟨(8205328639679480916589579055191137478909409670570956295060109657 /
    209520874727758242353680257618206333697874489361039360000000000000 : ℚ),
   (8205968210196667167126538301147963447923720778059929290458482343 /
    209520874727758242353680257618206333697874489361039360000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine216_eq :
    IntervalRat.cosComputable input216 10 = cosine216 := by gerver_interval_eq

theorem sine216_eq :
    IntervalRat.sinComputable input216 10 = sine216 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 217. -/
def input217 : IntervalRat :=
  ⟨(12837 /
    327680 : ℚ),
   (6419 /
    163840 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input217` at Taylor depth ten. -/
def cosine217 : IntervalRat :=
  ⟨(13011986808217476554436243474653913514480643946030365216474436163 /
    13021979588618345001194831859502081705134358957916160000000000000 : ℚ),
   (13011988365106295880026654018289733772976333397946693969824011197 /
    13021979588618345001194831859502081705134358957916160000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input217` at Taylor depth ten. -/
def sine217 : IntervalRat :=
  ⟨(510010957898579001953507302275892265752339055969211379978492483 /
    13021979588618345001194831859502081705134358957916160000000000000 : ℚ),
   (510050707992993076866361012544090090734055597554824987176707517 /
    13021979588618345001194831859502081705134358957916160000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine217_eq :
    IntervalRat.cosComputable input217 10 = cosine217 := by gerver_interval_eq

theorem sine217_eq :
    IntervalRat.sinComputable input217 10 = sine217 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 218. -/
def input218 : IntervalRat :=
  ⟨(401 /
    10240 : ℚ),
   (6417 /
    163840 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input218` at Taylor depth ten. -/
def cosine218 : IntervalRat :=
  ⟨(1124493225096019784653246013495120693933661876840121179264082847 /
    1125356260744795247016837321191537925135068058091520000000000000 : ℚ),
   (1124493494093588207708897103024158734967634656129088622419680353 /
    1125356260744795247016837321191537925135068058091520000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input218` at Taylor depth ten. -/
def sine218 : IntervalRat :=
  ⟨(44057860894835211005055515748718800945925486042038237206242207 /
    1125356260744795247016837321191537925135068058091520000000000000 : ℚ),
   (44064731280292277455204511774844718321751153155371891353885793 /
    1125356260744795247016837321191537925135068058091520000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine218_eq :
    IntervalRat.cosComputable input218 10 = cosine218 := by gerver_interval_eq

theorem sine218_eq :
    IntervalRat.sinComputable input218 10 = sine218 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 219. -/
def input219 : IntervalRat :=
  ⟨(6417 /
    163840 : ℚ),
   (3209 /
    81920 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input219` at Taylor depth ten. -/
def cosine219 : IntervalRat :=
  ⟨(44474574924877743824439622111887206291474228361562275200813671 /
    44508719297035358890802647957282505828095953469440000000000000 : ℚ),
   (44474585565599808362753486623916333590511391125901641361384089 /
    44508719297035358890802647957282505828095953469440000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input219` at Taylor depth ten. -/
def sine219 : IntervalRat :=
  ⟨(1742794269911638302265522588079174397724561037067584354969191 /
    44508719297035358890802647957282505828095953469440000000000000 : ℚ),
   (1743065999045604157146304610884598658746284332391530939750809 /
    44508719297035358890802647957282505828095953469440000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine219_eq :
    IntervalRat.cosComputable input219 10 = cosine219 := by gerver_interval_eq

theorem sine219_eq :
    IntervalRat.sinComputable input219 10 = sine219 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 220. -/
def input220 : IntervalRat :=
  ⟨(1603 /
    40960 : ℚ),
   (6413 /
    163840 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input220` at Taylor depth ten. -/
def cosine220 : IntervalRat :=
  ⟨(8280367122305282474081451925363468069207333257581179986545431873 /
    8286714283666219546214893001501324721449137518673920000000000000 : ℚ),
   (2760123033956914116826024151446462758127501634161251840477029269 /
    2762238094555406515404964333833774907149712506224640000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input220` at Taylor depth ten. -/
def sine220 : IntervalRat :=
  ⟨(108074636423113604969252693127945175130398156793090542383996011 /
    2762238094555406515404964333833774907149712506224640000000000000 : ℚ),
   (108091500091135809439970185752736105406757257098839218998403989 /
    2762238094555406515404964333833774907149712506224640000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine220_eq :
    IntervalRat.cosComputable input220 10 = cosine220 := by gerver_interval_eq

theorem sine220_eq :
    IntervalRat.sinComputable input220 10 = sine220 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 221. -/
def input221 : IntervalRat :=
  ⟨(6413 /
    163840 : ℚ),
   (3207 /
    81920 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input221` at Taylor depth ten. -/
def cosine221 : IntervalRat :=
  ⟨(549069351443761434805273606469178220378378272876749345582617 /
    549490361691794554207440098238055627507357450240000000000000 : ℚ),
   (78438497532688579423658173590936974614315805880107471899169 /
    78498623098827793458205728319722232501051064320000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input221` at Taylor depth ten. -/
def sine221 : IntervalRat :=
  ⟨(21502573632763303576934395102786564147336941014937711708697 /
    549490361691794554207440098238055627507357450240000000000000 : ℚ),
   (21505928312360651115675905404289895151418315706471861155303 /
    549490361691794554207440098238055627507357450240000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine221_eq :
    IntervalRat.cosComputable input221 10 = cosine221 := by gerver_interval_eq

theorem sine221_eq :
    IntervalRat.sinComputable input221 10 = sine221 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 222. -/
def input222 : IntervalRat :=
  ⟨(3207 /
    81920 : ℚ),
   (1283 /
    32768 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input222` at Taylor depth ten. -/
def cosine222 : IntervalRat :=
  ⟨(1165875133386933019398881705246712875373856232195559525628213 /
    1166769371140203712107056934611386520780038562629287936000000 : ℚ),
   (29146885304917021630187109561033814432101305317932363253279187 /
    29169234278505092802676423365284663019500964065732198400000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input222` at Taylor depth ten. -/
def sine222 : IntervalRat :=
  ⟨(45664958303846825109429214972049224498109002540490859133237 /
    1166769371140203712107056934611386520780038562629287936000000 : ℚ),
   (1304916614810110885665891475518646245905564436008391030073 /
    33336267746862963203058769560325329165143958932265369600000 : ℚ),
   by decide +kernel⟩

theorem cosine222_eq :
    IntervalRat.cosComputable input222 10 = cosine222 := by gerver_interval_eq

theorem sine222_eq :
    IntervalRat.sinComputable input222 10 = sine222 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 223. -/
def input223 : IntervalRat :=
  ⟨(1283 /
    32768 : ℚ),
   (401 /
    10240 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input223` at Taylor depth ten. -/
def cosine223 : IntervalRat :=
  ⟨(165680781748983361024783962894316982925594246580974793 /
    165807900194210405986020892699370182410240000000000000 : ℚ),
   (673242702735881691572150620813669103525616330270542359 /
    673759086503458157657481722714901058682880000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input223` at Taylor depth ten. -/
def sine223 : IntervalRat :=
  ⟨(67608251205822231167762278470333128743613994773533 /
    1727165627023025062354384298951772733440000000000000 : ℚ),
   (2504399840086501687947308784681635971784961466721 /
    63969097297149076383495714775991582720000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine223_eq :
    IntervalRat.cosComputable input223 10 = cosine223 := by gerver_interval_eq

theorem sine223_eq :
    IntervalRat.sinComputable input223 10 = sine223 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 224. -/
def input224 : IntervalRat :=
  ⟨(1283 /
    32768 : ℚ),
   (12831 /
    327680 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input224` at Taylor depth ten. -/
def cosine224 : IntervalRat :=
  ⟨(328994707307001671816687266143816263078475019222417978599735391207 /
    329247088857905809412926119114324238668088483281633280000000000000 : ℚ),
   (328994746649837228291330655990681532380857176955181446705250208793 /
    329247088857905809412926119114324238668088483281633280000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input224` at Taylor depth ten. -/
def sine224 : IntervalRat :=
  ⟨(12888063791264556694925705463052598073111880476057174232989791207 /
    329247088857905809412926119114324238668088483281633280000000000000 : ℚ),
   (12889068830408483917078515560943189811769397219559932997730208793 /
    329247088857905809412926119114324238668088483281633280000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine224_eq :
    IntervalRat.cosComputable input224 10 = cosine224 := by gerver_interval_eq

theorem sine224_eq :
    IntervalRat.sinComputable input224 10 = sine224 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 225. -/
def input225 : IntervalRat :=
  ⟨(12831 /
    327680 : ℚ),
   (401 /
    10240 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input225` at Taylor depth ten. -/
def cosine225 : IntervalRat :=
  ⟨(2650892508024243035458080890154589199529706012955045033 /
    2652926403107366495776334283189922918563840000000000000 : ℚ),
   (2714514252857340804286424246508774408278045000581844617033 /
    2716596636781943291674966305986481068609372160000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input225` at Taylor depth ten. -/
def sine225 : IntervalRat :=
  ⟨(811362249001922050029384287258828572453309948465021 /
    20725987524276300748252611587421272801280000000000000 : ℚ),
   (202856378965565487434890683024143356605697997535401 /
    5181496881069075187063152896855318200320000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine225_eq :
    IntervalRat.cosComputable input225 10 = cosine225 := by gerver_interval_eq

theorem sine225_eq :
    IntervalRat.sinComputable input225 10 = sine225 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 226. -/
def input226 : IntervalRat :=
  ⟨(641 /
    16384 : ℚ),
   (6411 /
    163840 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input226` at Taylor depth ten. -/
def cosine226 : IntervalRat :=
  ⟨(1124494838040611003593978899918215105419698464164310927153101469 /
    1125356260744795247016837321191537925135068058091520000000000000 : ℚ),
   (1124495106786642692818728341718980182751236163632884314728498531 /
    1125356260744795247016837321191537925135068058091520000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input226` at Taylor depth ten. -/
def sine226 : IntervalRat :=
  ⟨(44016680690197099126268964890297846198886292806831771031501469 /
    1125356260744795247016837321191537925135068058091520000000000000 : ℚ),
   (44023551072371536176881708560232554652006779814917108328498531 /
    1125356260744795247016837321191537925135068058091520000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine226_eq :
    IntervalRat.cosComputable input226 10 = cosine226 := by gerver_interval_eq

theorem sine226_eq :
    IntervalRat.sinComputable input226 10 = sine226 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 227. -/
def input227 : IntervalRat :=
  ⟨(6411 /
    163840 : ℚ),
   (1603 /
    40960 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input227` at Taylor depth ten. -/
def cosine227 : IntervalRat :=
  ⟨(3102304598774922653036376702480411007393729970909906974259 /
    3104681870607935190485675778270264078410711040000000000000 : ℚ),
   (3102305340318839380298235516120231723183958649948797291291 /
    3104681870607935190485675778270264078410711040000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input227` at Taylor depth ten. -/
def sine227 : IntervalRat :=
  ⟨(121454070942769190326137673048634608859589118692970557779 /
    3104681870607935190485675778270264078410711040000000000000 : ℚ),
   (121473025253882126155242399385020066562143111352053698221 /
    3104681870607935190485675778270264078410711040000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine227_eq :
    IntervalRat.cosComputable input227 10 = cosine227 := by gerver_interval_eq

theorem sine227_eq :
    IntervalRat.sinComputable input227 10 = sine227 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 228. -/
def input228 : IntervalRat :=
  ⟨(6419 /
    163840 : ℚ),
   (12839 /
    327680 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input228` at Taylor depth ten. -/
def cosine228 : IntervalRat :=
  ⟨(62179940189006282567666716732755219144258473801377116786729817332227 /
    62227699794144197979043036512607281108268723340228689920000000000000 : ℚ),
   (186539842888315583459098186892070416417759353230822573257282588144119 /
    186683099382432593937129109537821843324806170020686069760000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input228` at Taylor depth ten. -/
def sine228 : IntervalRat :=
  ⟨(812454040760615811086655134079374536615566072261390159475591126529 /
    20742566598048065993014345504202427036089574446742896640000000000000 : ℚ),
   (812517358246863497320538134915314929325263354211528683908020265471 /
    20742566598048065993014345504202427036089574446742896640000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine228_eq :
    IntervalRat.cosComputable input228 10 = cosine228 := by gerver_interval_eq

theorem sine228_eq :
    IntervalRat.sinComputable input228 10 = sine228 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 229. -/
def input229 : IntervalRat :=
  ⟨(12839 /
    327680 : ℚ),
   (321 /
    8192 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input229` at Taylor depth ten. -/
def cosine229 : IntervalRat :=
  ⟨(3431678521958667995717470426040351459056346620614313 /
    3434314760573715963796500613987847671920984064000000 : ℚ),
   (2745343146099426446411525522307964867747818973237383829 /
    2747451808458972771037200491190278137536787251200000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input229` at Taylor depth ten. -/
def sine229 : IntervalRat :=
  ⟨(134527235141303682368171185128765279741827709772319 /
    3434314760573715963796500613987847671920984064000000 : ℚ),
   (26907543704053109523376832084765027587268151052589 /
    686862952114743192759300122797569534384196812800000 : ℚ),
   by decide +kernel⟩

theorem cosine229_eq :
    IntervalRat.cosComputable input229 10 = cosine229 := by gerver_interval_eq

theorem sine229_eq :
    IntervalRat.sinComputable input229 10 = sine229 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 230. -/
def input230 : IntervalRat :=
  ⟨(6421 /
    163840 : ℚ),
   (12843 /
    327680 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input230` at Taylor depth ten. -/
def cosine230 : IntervalRat :=
  ⟨(2302959645522202338524375766609568979040680914929787038959468105533 /
    2304729622005340665890482833800269670676619382971432960000000000000 : ℚ),
   (2302959921179624849314635139960836574690647598908956214451474706627 /
    2304729622005340665890482833800269670676619382971432960000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input230` at Taylor depth ten. -/
def sine230 : IntervalRat :=
  ⟨(90300783503833551848939103492560171836900171306922492237716737853 /
    2304729622005340665890482833800269670676619382971432960000000000000 : ℚ),
   (90307818781204945219864426646591996965247422598429709169320702147 /
    2304729622005340665890482833800269670676619382971432960000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine230_eq :
    IntervalRat.cosComputable input230 10 = cosine230 := by gerver_interval_eq

theorem sine230_eq :
    IntervalRat.sinComputable input230 10 = sine230 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 231. -/
def input231 : IntervalRat :=
  ⟨(12843 /
    327680 : ℚ),
   (3211 /
    81920 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input231` at Taylor depth ten. -/
def cosine231 : IntervalRat :=
  ⟨(44474532356983436942081848375664565699768717902938197104431469 /
    44508719297035358890802647957282505828095953469440000000000000 : ℚ),
   (44474537680867887205709283367253116788945810805671641203903831 /
    44508719297035358890802647957282505828095953469440000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input231` at Taylor depth ten. -/
def sine231 : IntervalRat :=
  ⟨(1744015869589201250811407667340490327954671582638462470822189 /
    44508719297035358890802647957282505828095953469440000000000000 : ℚ),
   (1744151734202209918843412897904172773471822548527146661209811 /
    44508719297035358890802647957282505828095953469440000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine231_eq :
    IntervalRat.cosComputable input231 10 = cosine231 := by gerver_interval_eq

theorem sine231_eq :
    IntervalRat.sinComputable input231 10 = sine231 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 232. -/
def input232 : IntervalRat :=
  ⟨(157 /
    4000 : ℚ),
   (8647 /
    204800 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input232` at Taylor depth ten. -/
def cosine232 : IntervalRat :=
  ⟨(26505620601950607959591429732209933844374663106725153080600274876417 /
    26529264031073664957763342831899229185638400000000000000000000000000 : ℚ),
   (220906933933303375368034760967146119764988105326804379677088021032269 /
    221077200258947207981361190265826909880320000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input232` at Taylor depth ten. -/
def sine232 : IntervalRat :=
  ⟨(1982789071370668103036685677837004065487043931369729312620491973 /
    50531931487759361824311129203617579401216000000000000000000000000 : ℚ),
   (2132995264697111608947360573444319943730624529823657697433144123 /
    50531931487759361824311129203617579401216000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine232_eq :
    IntervalRat.cosComputable input232 10 = cosine232 := by gerver_interval_eq

theorem sine232_eq :
    IntervalRat.sinComputable input232 10 = sine232 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 233. -/
def input233 : IntervalRat :=
  ⟨(8647 /
    204800 : ℚ),
   (23139 /
    512000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input233` at Taylor depth ten. -/
def cosine233 : IntervalRat :=
  ⟨(312030178164878770736836613286505747983098378856720130504929942064981 /
    312349107896235724528787669804646400000000000000000000000000000000000 : ℚ),
   (312070747550450597556299412756646380956848883216011079614471262935019 /
    312349107896235724528787669804646400000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input233` at Taylor depth ten. -/
def sine233 : IntervalRat :=
  ⟨(1883345019221246455909086642458366328063761758576359323988766009283 /
    44621301128033674932683952829235200000000000000000000000000000000000 : ℚ),
   (14111911851721358711864199428697856310727723813254355797678637935019 /
    312349107896235724528787669804646400000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine233_eq :
    IntervalRat.cosComputable input233 10 = cosine233 := by gerver_interval_eq

theorem sine233_eq :
    IntervalRat.sinComputable input233 10 = sine233 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 234. -/
def input234 : IntervalRat :=
  ⟨(157 /
    4000 : ℚ),
   (83427 /
    2048000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input234` at Taylor depth ten. -/
def cosine234 : IntervalRat :=
  ⟨(0x2e4de2e6cd35d0805378337839f23d83064d9c257054d7ab69dc877ae8d5bd5 /
    0x2e57ba7c2f928138be324640000000000000000000000000000000000000000 : ℚ),
   (0x2e4e976051d2449e19f6f0b2cc5475c4e534df57c00dbf2e44637885172a42b /
    0x2e57ba7c2f928138be324640000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input234` at Taylor depth ten. -/
def sine234 : IntervalRat :=
  ⟨(51406698880418841386422313628990942073453436896332859631392263023667010517 /
    0x2e57ba7c2f928138be324640000000000000000000000000000000000000000 : ℚ),
   (7621971039676814670942431714463704744030137270768451215857157924710427069 /
    187155301806516154904856034087472516300800000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine234_eq :
    IntervalRat.cosComputable input234 10 = cosine234 := by gerver_interval_eq

theorem sine234_eq :
    IntervalRat.sinComputable input234 10 = sine234 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 235. -/
def input235 : IntervalRat :=
  ⟨(83427 /
    2048000 : ℚ),
   (8647 /
    204800 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input235` at Taylor depth ten. -/
def cosine235 : IntervalRat :=
  ⟨(3786517262303946985604939387734322830796903746720549701197170473911 /
    3789894861581952136823334690271318455091200000000000000000000000000 : ℚ),
   (662681396393641347684745563420701153000560563471991943582866883980903 /
    663231600776841623944083570797480729640960000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input235` at Taylor depth ten. -/
def sine235 : IntervalRat :=
  ⟨(8642966329460287963932929838735269687395251334764571348371706069 /
    212234112248589319662106742655193833485107200000000000000000000000 : ℚ),
   (44792013165942961642445890098167451328517856032736027826223360983 /
    1061170561242946598310533713275969167425536000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine235_eq :
    IntervalRat.cosComputable input235 10 = cosine235 := by gerver_interval_eq

theorem sine235_eq :
    IntervalRat.sinComputable input235 10 = sine235 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 236. -/
def input236 : IntervalRat :=
  ⟨(23139 /
    512000 : ℚ),
   (49321 /
    1024000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input236` at Taylor depth ten. -/
def cosine236 : IntervalRat :=
  ⟨(51754877018021554509248733146731182752385677672294308253010042614029641479 /
    51814968810690751870631528968553182003200000000000000000000000000000000000 : ℚ),
   (51762064564062153197606567103297613822490927430714983776930377968165558521 /
    51814968810690751870631528968553182003200000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input236` at Taylor depth ten. -/
def sine236 : IntervalRat :=
  ⟨(2340787194837801162772662632198026488464731035303716998974717610188105479 /
    51814968810690751870631528968553182003200000000000000000000000000000000000 : ℚ),
   (2494820552732741603451254524100194754928920370211765245830096172851894521 /
    51814968810690751870631528968553182003200000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine236_eq :
    IntervalRat.cosComputable input236 10 = cosine236 := by gerver_interval_eq

theorem sine236_eq :
    IntervalRat.sinComputable input236 10 = sine236 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 237. -/
def input237 : IntervalRat :=
  ⟨(49321 /
    1024000 : ℚ),
   (13091 /
    256000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input237` at Taylor depth ten. -/
def cosine237 : IntervalRat :=
  ⟨(12337502185686474830664518896375577975610099679341845926682594694509 /
    12353651240036666839273340456140800000000000000000000000000000000000 : ℚ),
   (8226216615881709526889639570277242626892477524091140067146674995869 /
    8235767493357777892848893637427200000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input237` at Taylor depth ten. -/
def sine237 : IntervalRat :=
  ⟨(198251600404089949260176572744442077052777442923620912490941608503 /
    4117883746678888946424446818713600000000000000000000000000000000000 : ℚ),
   (70164551937952382378678006888046267616239060130761575227286130499 /
    1372627915559629648808148939571200000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine237_eq :
    IntervalRat.cosComputable input237 10 = cosine237 := by gerver_interval_eq

theorem sine237_eq :
    IntervalRat.sinComputable input237 10 = sine237 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 238. -/
def input238 : IntervalRat :=
  ⟨(11339 /
    320000 : ℚ),
   (23069 /
    640000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input238` at Taylor depth ten. -/
def cosine238 : IntervalRat :=
  ⟨(294342678764688332146509583938538468813226134556714952032795123511480731 /
    294533997536579771978219520000000000000000000000000000000000000000000000 : ℚ),
   (3633939627886730956906313824541387870162247402828699217229618330811349 /
    3636222191809626814545920000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input238` at Taylor depth ten. -/
def sine238 : IntervalRat :=
  ⟨(3478122756891925274992284284393145389084062940678943587195530278973577 /
    98177999178859923992739840000000000000000000000000000000000000000000000 : ℚ),
   (3538116147386694597904874744282251111338227559274824285988213721026423 /
    98177999178859923992739840000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine238_eq :
    IntervalRat.cosComputable input238 10 = cosine238 := by gerver_interval_eq

theorem sine238_eq :
    IntervalRat.sinComputable input238 10 = sine238 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 239. -/
def input239 : IntervalRat :=
  ⟨(23069 /
    640000 : ℚ),
   (1173 /
    32000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input239` at Taylor depth ten. -/
def cosine239 : IntervalRat :=
  ⟨(3168404275580227694825059046682593720464527657761903717 /
    3170534137668829184000000000000000000000000000000000000 : ℚ),
   (35486916494158183643721571890333462087891970752099584515549 /
    35509982341890886860800000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input239` at Taylor depth ten. -/
def sine239 : IntervalRat :=
  ⟨(639840892101553752164518391263852242321761717450874883 /
    17754991170945443430400000000000000000000000000000000000 : ℚ),
   (650690470884538156674308971142276704859771192472129917 /
    17754991170945443430400000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine239_eq :
    IntervalRat.cosComputable input239 10 = cosine239 := by gerver_interval_eq

theorem sine239_eq :
    IntervalRat.sinComputable input239 10 = sine239 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 240. -/
def input240 : IntervalRat :=
  ⟨(48093 /
    1280000 : ℚ),
   (96577 /
    2560000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input240` at Taylor depth ten. -/
def cosine240 : IntervalRat :=
  ⟨(0xaa94664c09ac7db46466fbe24b9481e3942accfe788e9872298b53e78e0d6da3f /
    0xaab37e1bafdc580fe1e3807f63a72500000000000000000000000000000000000 : ℚ),
   (0x185e60f252d03d53ff8b0ecf05f44105fa5290027a1975ef33e3ec49fcbe729f7 /
    0x1862c8df62440c948dfbedc90e3c7300000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input240` at Taylor depth ten. -/
def sine240 : IntervalRat :=
  ⟨(0x669843e9847b09b9819fa78d4f5d4c89c09ca729e2c5f28b1ab5c3ed3721da3f /
    0xaab37e1bafdc580fe1e3807f63a72500000000000000000000000000000000000 : ℚ),
   (0x670314c60dfa4d32a6df5005043deafdb6983f7e3ae8016ef82244ee68de25c1 /
    0xaab37e1bafdc580fe1e3807f63a72500000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine240_eq :
    IntervalRat.cosComputable input240 10 = cosine240 := by gerver_interval_eq

theorem sine240_eq :
    IntervalRat.sinComputable input240 10 = sine240 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 241. -/
def input241 : IntervalRat :=
  ⟨(96577 /
    2560000 : ℚ),
   (12121 /
    320000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input241` at Taylor depth ten. -/
def cosine241 : IntervalRat :=
  ⟨(1149698167662443520181625628770325754512429882183805877853510663480557 /
    1150523427877264734289920000000000000000000000000000000000000000000000 : ℚ),
   (24527035954273927936950408477982937478281403689661948149538289452739159 /
    24544499794714980998184960000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input241` at Taylor depth ten. -/
def sine241 : IntervalRat :=
  ⟨(602688437401104080465086349114810147546674631551519290825872011631 /
    15979492053850899087360000000000000000000000000000000000000000000000 : ℚ),
   (86447090919241351402363250480796383177503884907441712641638819767 /
    2282784579121557012480000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine241_eq :
    IntervalRat.cosComputable input241 10 = cosine241 := by gerver_interval_eq

theorem sine241_eq :
    IntervalRat.sinComputable input241 10 = sine241 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 242. -/
def input242 : IntervalRat :=
  ⟨(1173 /
    32000 : ℚ),
   (47311 /
    1280000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input242` at Taylor depth ten. -/
def cosine242 : IntervalRat :=
  ⟨(54799421161904401525779163074639527163931725651266139020373848944436998099 /
    54836875177719579364672143360000000000000000000000000000000000000000000000 : ℚ),
   (54800037747427468938204233324506031757103120066940506328023367618763001901 /
    54836875177719579364672143360000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input242` at Taylor depth ten. -/
def sine242 : IntervalRat :=
  ⟨(287093791997017573067140927975981588388393176303588037996661037319571157 /
    7833839311102797052096020480000000000000000000000000000000000000000000000 : ℚ),
   (289487325504641411587637228842015823294922256790541787877258962680428843 /
    7833839311102797052096020480000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine242_eq :
    IntervalRat.cosComputable input242 10 = cosine242 := by gerver_interval_eq

theorem sine242_eq :
    IntervalRat.sinComputable input242 10 = sine242 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 243. -/
def input243 : IntervalRat :=
  ⟨(47311 /
    1280000 : ℚ),
   (23851 /
    640000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input243` at Taylor depth ten. -/
def cosine243 : IntervalRat :=
  ⟨(14015690001977348723570824699405487089436753725742377922142723949039769 /
    14025428454122846284677120000000000000000000000000000000000000000000000 : ℚ),
   (294332829263482476203021868808237225864735206935152366726824649542414851 /
    294533997536579771978219520000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input243` at Taylor depth ten. -/
def sine243 : IntervalRat :=
  ⟨(518283953095606589796492375877703363887547962663819900302646918279769 /
    14025428454122846284677120000000000000000000000000000000000000000000000 : ℚ),
   (3657984867902200138414456233918223971496318730627998584066559572041617 /
    98177999178859923992739840000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine243_eq :
    IntervalRat.cosComputable input243 10 = cosine243 := by gerver_interval_eq

theorem sine243_eq :
    IntervalRat.sinComputable input243 10 = sine243 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 244. -/
def input244 : IntervalRat :=
  ⟨(23851 /
    640000 : ℚ),
   (48093 /
    1280000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input244` at Taylor depth ten. -/
def cosine244 : IntervalRat :=
  ⟨(7441727187433113888469241298446668122853115301734386513185609882059002603 /
    7446983048826115716190044160000000000000000000000000000000000000000000000 : ℚ),
   (7441812311042828728215012436052157798108538608395951506897685936836357397 /
    7446983048826115716190044160000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input244` at Taylor depth ten. -/
def sine244 : IntervalRat :=
  ⟨(277462820176504887638536840914821625540659655879662890078164245328122603 /
    7446983048826115716190044160000000000000000000000000000000000000000000000 : ℚ),
   (279738171694493255011418814718548395712719099069649018766502634671877397 /
    7446983048826115716190044160000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine244_eq :
    IntervalRat.cosComputable input244 10 = cosine244 := by gerver_interval_eq

theorem sine244_eq :
    IntervalRat.sinComputable input244 10 = sine244 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 245. -/
def input245 : IntervalRat :=
  ⟨(48093 /
    1280000 : ℚ),
   (12121 /
    320000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input245` at Taylor depth ten. -/
def cosine245 : IntervalRat :=
  ⟨(143712270858933986802821249700790479981542749432749941547064202940929 /
    143815428484658091786240000000000000000000000000000000000000000000000 : ℚ),
   (1149711425420596720337473474944904373871343304145416670891782776250693 /
    1150523427877264734289920000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input245` at Taylor depth ten. -/
def sine245 : IntervalRat :=
  ⟨(5402235628431286187322174304497188669129894993940679304452504354679 /
    143815428484658091786240000000000000000000000000000000000000000000000 : ℚ),
   (5446177168670725121878969391575812522509096412032389549654495645321 /
    143815428484658091786240000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine245_eq :
    IntervalRat.cosComputable input245 10 = cosine245 := by gerver_interval_eq

theorem sine245_eq :
    IntervalRat.sinComputable input245 10 = sine245 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 246. -/
def input246 : IntervalRat :=
  ⟨(1173 /
    32000 : ℚ),
   (23851 /
    640000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input246` at Taylor depth ten. -/
def cosine246 : IntervalRat :=
  ⟨(294329489658251575661169062722219812540751312882029548713049754883875149 /
    294533997536579771978219520000000000000000000000000000000000000000000000 : ℚ),
   (294336140618859007108440987442335847837594542451285909224803582716124851 /
    294533997536579771978219520000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input246` at Taylor depth ten. -/
def sine246 : IntervalRat :=
  ⟨(10794012904635785465421111637131868065750563122444253767160577283875149 /
    294533997536579771978219520000000000000000000000000000000000000000000000 : ℚ),
   (10973995740578141240702909084151209879319987492944503265799422716124851 /
    294533997536579771978219520000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine246_eq :
    IntervalRat.cosComputable input246 10 = cosine246 := by gerver_interval_eq

theorem sine246_eq :
    IntervalRat.sinComputable input246 10 = sine246 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 247. -/
def input247 : IntervalRat :=
  ⟨(19941 /
    512000 : ℚ),
   (199801 /
    5120000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input247` at Taylor depth ten. -/
def cosine247 : IntervalRat :=
  ⟨(0xc2f041430072b4822dc5af07fe5a389b72b859df642bc4c08485aa9072c56fa5871 /
    0xc31646fb122064a46fdf6e4871e3980000000000000000000000000000000000000 : ℚ),
   (0xc2f0675375456bfb7bdc5a52a6600ba2d002522c4769110a0629c05dd3739a3a78f /
    0xc31646fb122064a46fdf6e4871e3980000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input247` at Taylor depth ten. -/
def sine247 : IntervalRat :=
  ⟨(0x7989f1a141c5d979075048d8253733803e71d76233f181500571d8c15710745871 /
    0xc31646fb122064a46fdf6e4871e3980000000000000000000000000000000000000 : ℚ),
   (0x79c6fb88206d260d029b1beb35e439edfd863817496a818c57626714866f8ba78f /
    0xc31646fb122064a46fdf6e4871e3980000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine247_eq :
    IntervalRat.cosComputable input247 10 = cosine247 := by gerver_interval_eq

theorem sine247_eq :
    IntervalRat.sinComputable input247 10 = sine247 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 248. -/
def input248 : IntervalRat :=
  ⟨(199801 /
    5120000 : ℚ),
   (391 /
    10000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input248` at Taylor depth ten. -/
def cosine248 : IntervalRat :=
  ⟨(1903447961837263989401821285376931219956527626577907646714221 /
    1904903895121920000000000000000000000000000000000000000000000 : ℚ),
   (4490810569049892661377751595604149012660982506595275160896720554709 /
    4494232140145565368320000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input248` at Taylor depth ten. -/
def sine248 : IntervalRat :=
  ⟨(3567231867982512139223915506511376576940655630994332588655733 /
    91435386965852160000000000000000000000000000000000000000000000 : ℚ),
   (6980891224956666541851185648550314367275968426045647108491 /
    178584740167680000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine248_eq :
    IntervalRat.cosComputable input248 10 = cosine248 := by gerver_interval_eq

theorem sine248_eq :
    IntervalRat.sinComputable input248 10 = sine248 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 249. -/
def input249 : IntervalRat :=
  ⟨(12121 /
    320000 : ℚ),
   (97359 /
    2560000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input249` at Taylor depth ten. -/
def cosine249 : IntervalRat :=
  ⟨(0x21b1c1c163c67a1756a57f4c8e6a22a2466e2c9b5c816784d985e4312a247341 /
    0x21b7ffa0554e4a48ab0a2c585f89500000000000000000000000000000000000 : ℚ),
   (0x4d04214ae4e262573e4950af368f985ed41fb7aef6f8690637284cbcf43ef89 /
    0x4d124849e78e60a6193bd313238300000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input249` at Taylor depth ten. -/
def sine249 : IntervalRat :=
  ⟨(577555993920008097036044976331593542834342066406201549146628250699942884161 /
    0x21b7ffa0554e4a48ab0a2c585f89500000000000000000000000000000000000 : ℚ),
   (579885969526609379246777330856606042241763340598852259008722019252057115839 /
    0x21b7ffa0554e4a48ab0a2c585f89500000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine249_eq :
    IntervalRat.cosComputable input249 10 = cosine249 := by gerver_interval_eq

theorem sine249_eq :
    IntervalRat.sinComputable input249 10 = sine249 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 250. -/
def input250 : IntervalRat :=
  ⟨(97359 /
    2560000 : ℚ),
   (391 /
    10240 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input250` at Taylor depth ten. -/
def cosine250 : IntervalRat :=
  ⟨(252818362265985368855018258612101046685435724037360098884517 /
    253002777395950936868318012541763584000000000000000000000000 : ℚ),
   (3950309918966680060799131736283065624871825882088157908611152723 /
    3953168396811733388567468945965056000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input250` at Taylor depth ten. -/
def sine250 : IntervalRat :=
  ⟨(48097875569779813680131040156611320313360616770096141327801 /
    1265013886979754684341590062708817920000000000000000000000000 : ℚ),
   (386329067525155688728077792704075524154803122538589211923 /
    10120111095838037474732720501670543360000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine250_eq :
    IntervalRat.cosComputable input250 10 = cosine250 := by gerver_interval_eq

theorem sine250_eq :
    IntervalRat.sinComputable input250 10 = sine250 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 251. -/
def input251 : IntervalRat :=
  ⟨(391 /
    10240 : ℚ),
   (98141 /
    2560000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input251` at Taylor depth ten. -/
def cosine251 : IntervalRat :=
  ⟨(0xaa93626efe33b6a4ce37c0c30669814ccf82d7bc50ba6e402f77f86089d5271db /
    0xaab37e1bafdc580fe1e3807f63a72500000000000000000000000000000000000 : ℚ),
   (0x38dbe144d147ec3149d491f5fe27fd4ea1ee2669f912ebc0e28c9cb5d2b0f84b7 /
    0x38e67f5e8ff41d5aa0a12ad52137b700000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input251` at Taylor depth ten. -/
def sine251 : IntervalRat :=
  ⟨(0xb95ae12c89e7a90aecd943ed54e5df580ea6c1057a9d4aca003f0fc614ed3c3 /
    0x12f77fca2ffc09c8e035b8f1b5bd3d00000000000000000000000000000000000 : ℚ),
   (0x22e4a53e9067a0b239689ce2b767a11320ab66ebf8e8ee9dbfe162f3bc1384b7 /
    0x38e67f5e8ff41d5aa0a12ad52137b700000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine251_eq :
    IntervalRat.cosComputable input251 10 = cosine251 := by gerver_interval_eq

theorem sine251_eq :
    IntervalRat.sinComputable input251 10 = sine251 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 252. -/
def input252 : IntervalRat :=
  ⟨(98141 /
    2560000 : ℚ),
   (24633 /
    640000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input252` at Taylor depth ten. -/
def cosine252 : IntervalRat :=
  ⟨(519075593922618613363750668610973135870250590845810293030391683245549 /
    519460313115660973506560000000000000000000000000000000000000000000000 : ℚ),
   (2076314566258450127702882047158795851162271888932365333153129136664679 /
    2077841252462643894026240000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input252` at Taylor depth ten. -/
def sine252 : IntervalRat :=
  ⟨(19909284530255528012346401230614328995643331999322775697427470238049 /
    519460313115660973506560000000000000000000000000000000000000000000000 : ℚ),
   (19988643489236063743604810133919307732685863133651212741088529761951 /
    519460313115660973506560000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine252_eq :
    IntervalRat.cosComputable input252 10 = cosine252 := by gerver_interval_eq

theorem sine252_eq :
    IntervalRat.sinComputable input252 10 = sine252 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 253. -/
def input253 : IntervalRat :=
  ⟨(24633 /
    640000 : ℚ),
   (98923 /
    2560000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input253` at Taylor depth ten. -/
def cosine253 : IntervalRat :=
  ⟨(0xf81b72d153fbc075522ac8a9f6c561c849c00644ba94ae8283250a45d6e58fc7 /
    0xf84ae5f9b9faaea2bcedd22da838f00000000000000000000000000000000000 : ℚ),
   (0xf81bd2aa2a753538f3e99cdbee6425887113767b247e62ba53f8769ef48a7039 /
    0xf84ae5f9b9faaea2bcedd22da838f00000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input253` at Taylor depth ten. -/
def sine253 : IntervalRat :=
  ⟨(0x98dde1916f39c213e01d5e222a89f25fc7c85a6e016dc86a67f0340da758fc7 /
    0xf84ae5f9b9faaea2bcedd22da838f00000000000000000000000000000000000 : ℚ),
   (0x99794060012dbb7e5137b9262af84ab082c872c0cab5a04ad4c2075258a7039 /
    0xf84ae5f9b9faaea2bcedd22da838f00000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine253_eq :
    IntervalRat.cosComputable input253 10 = cosine253 := by gerver_interval_eq

theorem sine253_eq :
    IntervalRat.sinComputable input253 10 = sine253 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 254. -/
def input254 : IntervalRat :=
  ⟨(98923 /
    2560000 : ℚ),
   (49657 /
    1280000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input254` at Taylor depth ten. -/
def cosine254 : IntervalRat :=
  ⟨(602751766478197841706310700820253403316073892949576639013948914559650224407 /
    603205626954915373011393576960000000000000000000000000000000000000000000000 : ℚ),
   (9567544977646854997819398193123810954307977106716268053567935797014512311 /
    9574692491347863063672913920000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input254` at Taylor depth ten. -/
def sine254 : IntervalRat :=
  ⟨(2589233669430830538356974589070921536179050131173125550654665926427793823 /
    67022847439435041445710397440000000000000000000000000000000000000000000000 : ℚ),
   (7798418759874644987882825918800494498390588071529658108184701868716618531 /
    201068542318305124337131192320000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine254_eq :
    IntervalRat.cosComputable input254 10 = cosine254 := by gerver_interval_eq

theorem sine254_eq :
    IntervalRat.sinComputable input254 10 = sine254 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 255. -/
def input255 : IntervalRat :=
  ⟨(49657 /
    1280000 : ℚ),
   (19941 /
    512000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input255` at Taylor depth ten. -/
def cosine255 : IntervalRat :=
  ⟨(1560561190325973141811670007118159839960847793619500077896085125980639 /
    1561745539481178622643938349023232000000000000000000000000000000000000 : ℚ),
   (39014261557201871772935701870719098676066297986040857912978856109142329 /
    39043638487029465566098458725580800000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input255` at Taylor depth ten. -/
def sine255 : IntervalRat :=
  ⟨(12114373988828116499837781560747082595823974079498272956426083406739 /
    312349107896235724528787669804646400000000000000000000000000000000000 : ℚ),
   (1737441778445077121806028904397284532914723890542043791913361074923 /
    44621301128033674932683952829235200000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine255_eq :
    IntervalRat.cosComputable input255 10 = cosine255 := by gerver_interval_eq

theorem sine255_eq :
    IntervalRat.sinComputable input255 10 = sine255 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 256. -/
def input256 : IntervalRat :=
  ⟨(19941 /
    512000 : ℚ),
   (391 /
    10000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input256` at Taylor depth ten. -/
def cosine256 : IntervalRat :=
  ⟨(1070689478127059708097177017302072083632535660423580413833429 /
    1071508441006080000000000000000000000000000000000000000000000 : ℚ),
   (10024160597353301875952561786565363504960564351002635770965442883 /
    10031768169967779840000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input256` at Taylor depth ten. -/
def sine256 : IntervalRat :=
  ⟨(333773529696619415890320788444348436402400066415903569651807 /
    8572067528048640000000000000000000000000000000000000000000000 : ℚ),
   (1308918403883119750742743062653553236707561036358942011553 /
    33484638781440000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine256_eq :
    IntervalRat.cosComputable input256 10 = cosine256 := by gerver_interval_eq

theorem sine256_eq :
    IntervalRat.sinComputable input256 10 = sine256 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 257. -/
def input257 : IntervalRat :=
  ⟨(12121 /
    320000 : ℚ),
   (391 /
    10240 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input257` at Taylor depth ten. -/
def cosine257 : IntervalRat :=
  ⟨(84272787362599387969416491075041647280019392664605083663799 /
    84334259131983645622772670847254528000000000000000000000000 : ℚ),
   (3950332832524481504866212083875930632193507660074244566322900147 /
    3953168396811733388567468945965056000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input257` at Taylor depth ten. -/
def sine257 : IntervalRat :=
  ⟨(15968237134705181457718068987039631576076605340642632758419 /
    421671295659918228113863354236272640000000000000000000000000 : ℚ),
   (42925534906836805849929780800857083181507979907193549627 /
    1124456788426448608303635611296727040000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine257_eq :
    IntervalRat.cosComputable input257 10 = cosine257 := by gerver_interval_eq

theorem sine257_eq :
    IntervalRat.sinComputable input257 10 = sine257 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 258. -/
def input258 : IntervalRat :=
  ⟨(391 /
    10240 : ℚ),
   (24633 /
    640000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input258` at Taylor depth ten. -/
def cosine258 : IntervalRat :=
  ⟨(519075593547899658551235461027691459793817624340816674649552345238049 /
    519460313115660973506560000000000000000000000000000000000000000000000 : ℚ),
   (519081676714026392306987492236720948341125339265422767945662498511951 /
    519460313115660973506560000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input258` at Taylor depth ten. -/
def sine258 : IntervalRat :=
  ⟨(19829964668707587367773264504412606842798519166598830870255470238049 /
    519460313115660973506560000000000000000000000000000000000000000000000 : ℚ),
   (19988682431177397078636961744115594164615655483182419129744529761951 /
    519460313115660973506560000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine258_eq :
    IntervalRat.cosComputable input258 10 = cosine258 := by gerver_interval_eq

theorem sine258_eq :
    IntervalRat.sinComputable input258 10 = sine258 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 259. -/
def input259 : IntervalRat :=
  ⟨(24633 /
    640000 : ℚ),
   (49657 /
    1280000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input259` at Taylor depth ten. -/
def cosine259 : IntervalRat :=
  ⟨(602751766032604866628222650201349850416282866074865860698928607788661024407 /
    603205626954915373011393576960000000000000000000000000000000000000000000000 : ℚ),
   (602758886188258700251112287895781807148595098240625341863505471462692575593 /
    603205626954915373011393576960000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input259` at Taylor depth ten. -/
def sine259 : IntervalRat :=
  ⟨(23210995894866791129354048470210062439972767678397877671336872185850144407 /
    603205626954915373011393576960000000000000000000000000000000000000000000000 : ℚ),
   (23395302222367334541469974944425533181851396296278957489195841286149855593 /
    603205626954915373011393576960000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine259_eq :
    IntervalRat.cosComputable input259 10 = cosine259 := by gerver_interval_eq

theorem sine259_eq :
    IntervalRat.sinComputable input259 10 = sine259 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 260. -/
def input260 : IntervalRat :=
  ⟨(49657 /
    1280000 : ℚ),
   (391 /
    10000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input260` at Taylor depth ten. -/
def cosine260 : IntervalRat :=
  ⟨(22306030777430112304196435269917191513872084721331505700423 /
    22323092520960000000000000000000000000000000000000000000000 : ℚ),
   (1096399078643235252312387344012213268940663979297376715018831829 /
    1097224643590225920000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input260` at Taylor depth ten. -/
def sine260 : IntervalRat :=
  ⟨(494739008695808650208725924702104337041960658576982935331 /
    12756052869120000000000000000000000000000000000000000000000 : ℚ),
   (3895598198380117356449962009811749595391063392532954973 /
    99656663040000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine260_eq :
    IntervalRat.cosComputable input260 10 = cosine260 := by gerver_interval_eq

theorem sine260_eq :
    IntervalRat.sinComputable input260 10 = sine260 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 261. -/
def input261 : IntervalRat :=
  ⟨(23851 /
    640000 : ℚ),
   (12121 /
    320000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input261` at Taylor depth ten. -/
def cosine261 : IntervalRat :=
  ⟨(143712270662394384059127934630882487773725269969150077164155737734679 /
    143815428484658091786240000000000000000000000000000000000000000000000 : ℚ),
   (47905190626697051773047744443822484660328740957866293449750164730107 /
    47938476161552697262080000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input261` at Taylor depth ten. -/
def sine261 : IntervalRat :=
  ⟨(1786105004033691838719534333482676078141558099293664485233834784893 /
    47938476161552697262080000000000000000000000000000000000000000000000 : ℚ),
   (1815399307706569620276053726783418580411309221256998901038165215107 /
    47938476161552697262080000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine261_eq :
    IntervalRat.cosComputable input261 10 = cosine261 := by gerver_interval_eq

theorem sine261_eq :
    IntervalRat.sinComputable input261 10 = sine261 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 262. -/
def input262 : IntervalRat :=
  ⟨(12121 /
    320000 : ℚ),
   (24633 /
    640000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input262` at Taylor depth ten. -/
def cosine262 : IntervalRat :=
  ⟨(519075592802949401102588813245102022943677965669041808384078323358049 /
    519460313115660973506560000000000000000000000000000000000000000000000 : ℚ),
   (519087710663758469114279126964151282779136575091750416968780822881951 /
    519460313115660973506560000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input262` at Taylor depth ten. -/
def sine262 : IntervalRat :=
  ⟨(19671324945714383255574529185095281533351039549261056720751470238049 /
    519460313115660973506560000000000000000000000000000000000000000000000 : ℚ),
   (19988759848689504090275159010460304031950108570183652655248529761951 /
    519460313115660973506560000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine262_eq :
    IntervalRat.cosComputable input262 10 = cosine262 := by gerver_interval_eq

theorem sine262_eq :
    IntervalRat.sinComputable input262 10 = sine262 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 263. -/
def input263 : IntervalRat :=
  ⟨(24633 /
    640000 : ℚ),
   (391 /
    10000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input263` at Taylor depth ten. -/
def cosine263 : IntervalRat :=
  ⟨(4182380764474100676394524501293432278062546910687729815509 /
    4185579847680000000000000000000000000000000000000000000000 : ℚ),
   (17131437945015232811733372069153519347345980756834920424978261 /
    17144135056097280000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input263` at Taylor depth ten. -/
def sine263 : IntervalRat :=
  ⟨(322115998182898439063478946372781805905478010458182954143 /
    8371159695360000000000000000000000000000000000000000000000 : ℚ),
   (5112992756489684880320187431993996165286557655145182113 /
    130799370240000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine263_eq :
    IntervalRat.cosComputable input263 10 = cosine263 := by gerver_interval_eq

theorem sine263_eq :
    IntervalRat.sinComputable input263 10 = sine263 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 264. -/
def input264 : IntervalRat :=
  ⟨(157 /
    4000 : ℚ),
   (163811 /
    4096000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input264` at Taylor depth ten. -/
def cosine264 : IntervalRat :=
  ⟨(0x75360cd98cb0f13632df3761f7b5740360058223f445d3f0657f50f775668a26065 /
    0x754e100a586ad717a16f41d20000000000000000000000000000000000000000000 : ℚ),
   (0xd061a923f82d4c7fac5f8eff71d027998723705e0e6bc4c7b041b72ba110d18383 /
    0xd08ac72ed613457f57e23c20000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input264` at Taylor depth ten. -/
def sine264 : IntervalRat :=
  ⟨(0x2ba4a74027917a6b3178296b39c8207c9147c5a6b281f156fea1846ca4fba297f /
    0x458397ba475bc1d51d4b6960000000000000000000000000000000000000000000 : ℚ),
   (0x1903a28aaee34cf145fb3d9197a60dc9fef37cbe09b3431690c52582e332748a89 /
    0x271a0558c8239d07e07a6b460000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine264_eq :
    IntervalRat.cosComputable input264 10 = cosine264 := by gerver_interval_eq

theorem sine264_eq :
    IntervalRat.sinComputable input264 10 = sine264 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 265. -/
def input265 : IntervalRat :=
  ⟨(163811 /
    4096000 : ℚ),
   (83427 /
    2048000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input265` at Taylor depth ten. -/
def cosine265 : IntervalRat :=
  ⟨(0x2e4de2e9f75a6874eac775f0932e7dd2504e75cabdafaeef54331a33bc03fd5 /
    0x2e57ba7c2f928138be324640000000000000000000000000000000000000000 : ℚ),
   (0x2e4e3dfd49d3e9c71cde2351edf1f4b05a8908c450126a9373a455013db5d2b /
    0x2e57ba7c2f928138be324640000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input265` at Taylor depth ten. -/
def sine265 : IntervalRat :=
  ⟨(52379719578258037598074186200406243531338013809679143083563804568627010517 /
    0x2e57ba7c2f928138be324640000000000000000000000000000000000000000 : ℚ),
   (53353273686897224125318755509058315107375685956021857841995474228172989483 /
    0x2e57ba7c2f928138be324640000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine265_eq :
    IntervalRat.cosComputable input265 10 = cosine265 := by gerver_interval_eq

theorem sine265_eq :
    IntervalRat.sinComputable input265 10 = sine265 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 266. -/
def input266 : IntervalRat :=
  ⟨(83427 /
    2048000 : ℚ),
   (169897 /
    4096000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input266` at Taylor depth ten. -/
def cosine266 : IntervalRat :=
  ⟨(0x10be51aa82503f65db1876a0ad6b14380f50459243a24ab3cacdc21ca66668c1601 /
    0x10c2024a9eeab1036034771e0000000000000000000000000000000000000000000 : ℚ),
   (0x10be7334abd4a4e007f2de75bfb1cf93cc34b6b970da3ce8fb617319db2f20be9ff /
    0x10c2024a9eeab1036034771e0000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input266` at Taylor depth ten. -/
def sine266 : IntervalRat :=
  ⟨(0xaeb4fea38567beafccd87c9b3902efe38a3025002689697a1a9622db281d41601 /
    0x10c2024a9eeab1036034771e0000000000000000000000000000000000000000000 : ℚ),
   (0xb1e5216b9ea41ad32b97cf4e333a0fca91f31853cae97da6ed394ff857e2be9ff /
    0x10c2024a9eeab1036034771e0000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine266_eq :
    IntervalRat.cosComputable input266 10 = cosine266 := by gerver_interval_eq

theorem sine266_eq :
    IntervalRat.sinComputable input266 10 = sine266 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 267. -/
def input267 : IntervalRat :=
  ⟨(169897 /
    4096000 : ℚ),
   (8647 /
    204800 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input267` at Taylor depth ten. -/
def cosine267 : IntervalRat :=
  ⟨(26505620956478743893804927808364668464353422505286219342507367126177 /
    26529264031073664957763342831899229185638400000000000000000000000000 : ℚ),
   (220887048228637927001584665471323571479982635539992904184238131423099 /
    221077200258947207981361190265826909880320000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input267` at Taylor depth ten. -/
def sine267 : IntervalRat :=
  ⟨(1629739341656686150793231989772789334720318294962994366215039243 /
    39302613379368392530019767158369228423168000000000000000000000000 : ℚ),
   (4976839678472127509643411606495321121700365384814106201886065887 /
    117907840138105177590059301475107685269504000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine267_eq :
    IntervalRat.cosComputable input267 10 = cosine267 := by gerver_interval_eq

theorem sine267_eq :
    IntervalRat.sinComputable input267 10 = sine267 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 268. -/
def input268 : IntervalRat :=
  ⟨(8647 /
    204800 : ℚ),
   (175983 /
    4096000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input268` at Taylor depth ten. -/
def cosine268 : IntervalRat :=
  ⟨(0x34ea08cfd8553a5f5baeb5511fb14bdcea4dde8c1af967e6e9f51e4cc840a37d7 /
    0x34f68bfba41525f7b4cbbe0000000000000000000000000000000000000000000 : ℚ),
   (0x172693e84864116f6437c94737b72afc5cb70a09286c3f4ae841d140e96c38791f /
    0x172bdd3e17c9409c5f192320000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input268` at Taylor depth ten. -/
def sine268 : IntervalRat :=
  ⟨(0xfa605036aac9ad6bf2dd8952c2b57a391afc3243627e2f43325db543dbc786e1 /
    0x172bdd3e17c9409c5f192320000000000000000000000000000000000000000000 : ℚ),
   (0xfec8d2255a86b4e0ec63ab9a78fc664216b637f2c867c905a95f553c2438791f /
    0x172bdd3e17c9409c5f192320000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine268_eq :
    IntervalRat.cosComputable input268 10 = cosine268 := by gerver_interval_eq

theorem sine268_eq :
    IntervalRat.sinComputable input268 10 = sine268 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 269. -/
def input269 : IntervalRat :=
  ⟨(175983 /
    4096000 : ℚ),
   (89513 /
    2048000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input269` at Taylor depth ten. -/
def cosine269 : IntervalRat :=
  ⟨(0xea62c42bb698681404538ae912f4afaa664ef0bcd251c2b69483f3b816ecbc07 /
    0xea9c2014b0d5ae2f42de83a40000000000000000000000000000000000000000 : ℚ),
   (0x217c19990c6d1cb94b8cc4e7d01a52d605d338cf32ba4be056c2f7cfa7dbceff /
    0x218404953dd56206c068ee3c0000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input269` at Taylor depth ten. -/
def sine269 : IntervalRat :=
  ⟨(0xa13a3416b4ad526a792e2cd5be3d93cfdd4e65b9062fabb943917f9871a7807 /
    0xea9c2014b0d5ae2f42de83a40000000000000000000000000000000000000000 : ℚ),
   (0xa4045841a59d57fbe196a4936ff5b0548730baec1ea514d4544348a47e587f9 /
    0xea9c2014b0d5ae2f42de83a40000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine269_eq :
    IntervalRat.cosComputable input269 10 = cosine269 := by gerver_interval_eq

theorem sine269_eq :
    IntervalRat.sinComputable input269 10 = sine269 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 270. -/
def input270 : IntervalRat :=
  ⟨(89513 /
    2048000 : ℚ),
   (23139 /
    512000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input270` at Taylor depth ten. -/
def cosine270 : IntervalRat :=
  ⟨(312030181558485220922231451959154899328383765310152008898618689162981 /
    312349107896235724528787669804646400000000000000000000000000000000000 : ℚ),
   (78012702760245563321570007105921947368923481536491919006218281866911 /
    78087276974058931132196917451161600000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input270` at Taylor depth ten. -/
def sine270 : IntervalRat :=
  ⟨(13647357944998980640235079203961818442034573109664636408153042064981 /
    312349107896235724528787669804646400000000000000000000000000000000000 : ℚ),
   (14111611498662070631147172457151478049657056455077259235082797935019 /
    312349107896235724528787669804646400000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine270_eq :
    IntervalRat.cosComputable input270 10 = cosine270 := by gerver_interval_eq

theorem sine270_eq :
    IntervalRat.sinComputable input270 10 = sine270 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 271. -/
def input271 : IntervalRat :=
  ⟨(23139 /
    512000 : ℚ),
   (95599 /
    2048000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input271` at Taylor depth ten. -/
def cosine271 : IntervalRat :=
  ⟨(0x217aabfa50c52d588b5df3f3a9a5e11d08771cf8ddff08b84853b0c7df39fd07 /
    0x218404953dd56206c068ee3c0000000000000000000000000000000000000000 : ℚ),
   (0x217b41e5849a67c40a87b2296d2a20540985f7f876dd7952470c418d768602f9 /
    0x218404953dd56206c068ee3c0000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input271` at Taylor depth ten. -/
def sine271 : IntervalRat :=
  ⟨(684863543319341686059807443976943611791823101255946937575652494465637678343 /
    0x218404953dd56206c068ee3c0000000000000000000000000000000000000000 : ℚ),
   (707396170959431811946962077741023518268670709864087216907853303063962321657 /
    0x218404953dd56206c068ee3c0000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine271_eq :
    IntervalRat.cosComputable input271 10 = cosine271 := by gerver_interval_eq

theorem sine271_eq :
    IntervalRat.sinComputable input271 10 = sine271 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 272. -/
def input272 : IntervalRat :=
  ⟨(95599 /
    2048000 : ℚ),
   (49321 /
    1024000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input272` at Taylor depth ten. -/
def cosine272 : IntervalRat :=
  ⟨(17251625900556263427721471819907574110918931999083350307847498542132440493 /
    17271656270230250623543842989517727334400000000000000000000000000000000000 : ℚ),
   (51758528671165594772460187451907976168934265411299905410565197683845638521 /
    51814968810690751870631528968553182003200000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input272` at Taylor depth ten. -/
def sine272 : IntervalRat :=
  ⟨(805915394031877537399251690957284714379406647976231413047366118809368493 /
    17271656270230250623543842989517727334400000000000000000000000000000000000 : ℚ),
   (831587926512134682085332058106550214791091679934769702761517224550631507 /
    17271656270230250623543842989517727334400000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine272_eq :
    IntervalRat.cosComputable input272 10 = cosine272 := by gerver_interval_eq

theorem sine272_eq :
    IntervalRat.sinComputable input272 10 = sine272 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 273. -/
def input273 : IntervalRat :=
  ⟨(89513 /
    2048000 : ℚ),
   (182069 /
    4096000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input273` at Taylor depth ten. -/
def cosine273 : IntervalRat :=
  ⟨(0x7530666a29af349cd7825ac7226735c57ec74839e17d1e197a0bf255a512c750f93 /
    0x754e100a586ad717a16f41d20000000000000000000000000000000000000000000 : ℚ),
   (0x594a32694bfdb5f9c5acf26a46c7164d7871afa6b211770cae7757f399abc26cf9 /
    0x59600c38a4e3b0120117d0a0000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input273` at Taylor depth ten. -/
def sine273 : IntervalRat :=
  ⟨(0x91ca2a3d06bac1c37df942afda400914089188b34fb449ebbc72e7edf910501bb /
    0xd08ac72ed613457f57e23c20000000000000000000000000000000000000000000 : ℚ),
   (0x1bccee470482ec3eff0e069578e6f67bb0b8978723a860351c9ae52af94cf0facf /
    0x271a0558c8239d07e07a6b460000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine273_eq :
    IntervalRat.cosComputable input273 10 = cosine273 := by gerver_interval_eq

theorem sine273_eq :
    IntervalRat.sinComputable input273 10 = sine273 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 274. -/
def input274 : IntervalRat :=
  ⟨(182069 /
    4096000 : ℚ),
   (23139 /
    512000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input274` at Taylor depth ten. -/
def cosine274 : IntervalRat :=
  ⟨(156015091649649355301165272414567053366840694211985309953961290069303 /
    156174553948117862264393834902323200000000000000000000000000000000000 : ℚ),
   (19970597391230412664814520679488181311499191976938412146453894867784841 /
    19990342905359086369842410867497369600000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input274` at Taylor depth ten. -/
def sine274 : IntervalRat :=
  ⟨(13879329351371739157269162018480282416324240205888924164967682064981 /
    312349107896235724528787669804646400000000000000000000000000000000000 : ℚ),
   (14111457426979018043522344661872100961330372317285324792525997935019 /
    312349107896235724528787669804646400000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine274_eq :
    IntervalRat.cosComputable input274 10 = cosine274 := by gerver_interval_eq

theorem sine274_eq :
    IntervalRat.sinComputable input274 10 = sine274 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 275. -/
def input275 : IntervalRat :=
  ⟨(23139 /
    512000 : ℚ),
   (37631 /
    819200 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input275` at Taylor depth ten. -/
def cosine275 : IntervalRat :=
  ⟨(10104947144467355310202722105760263895940657194417086693623838599968606187 /
    10115618022053490657000601808473296779112716697600000000000000000000000000 : ℚ),
   (252632239209468054359937908141913122282873611606928787836065112383023413773 /
    252890450551337266425015045211832419477817917440000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input275` at Taylor depth ten. -/
def sine275 : IntervalRat :=
  ⟨(3655983989526331920216333248747550232465309340908135708953295842115207 /
    80924944176427925256004814467786374232901733580800000000000000000000000 : ℚ),
   (18580627734098386956922874063524889278606961454692610163980285610624861 /
    404624720882139626280024072338931871164508667904000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine275_eq :
    IntervalRat.cosComputable input275 10 = cosine275 := by gerver_interval_eq

theorem sine275_eq :
    IntervalRat.sinComputable input275 10 = sine275 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 276. -/
def input276 : IntervalRat :=
  ⟨(37631 /
    819200 : ℚ),
   (95599 /
    2048000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input276` at Taylor depth ten. -/
def cosine276 : IntervalRat :=
  ⟨(0x217aabfdc5819f0445008b8fac511c446bd58e7f078993757c080271b7651907 /
    0x218404953dd56206c068ee3c0000000000000000000000000000000000000000 : ℚ),
   (0x3b854652c0768403910a8cbccf60656681c74a43a1aaa1de4bda5ca59989e71 /
    0x3b955d7b1897cab6ab6535c0000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input276` at Taylor depth ten. -/
def sine276 : IntervalRat :=
  ⟨(25782289191030629184910994051832528000541081237685509647617804858656210309 /
    561465905419548464714568102262417548902400000000000000000000000000000000000 : ℚ),
   (235796062362023445024725178834387814535408226334731541770076709872094107219 /
    0xb2c0187149c76024022fa140000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine276_eq :
    IntervalRat.cosComputable input276 10 = cosine276 := by gerver_interval_eq

theorem sine276_eq :
    IntervalRat.sinComputable input276 10 = sine276 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 277. -/
def input277 : IntervalRat :=
  ⟨(8647 /
    204800 : ℚ),
   (89513 /
    2048000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input277` at Taylor depth ten. -/
def cosine277 : IntervalRat :=
  ⟨(0x4e20ec07f6512029a91b7f1e9e371a2d3ad3140c1e993d280c76a41cc234d2ad /
    0x4e340ab190473a0fc0f4d68c0000000000000000000000000000000000000000 : ℚ),
   (0xea6699a2b00239b72bbc11b661669fa118591fa8ef396ab25a3379996f7587f9 /
    0xea9c2014b0d5ae2f42de83a40000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input277` at Taylor depth ten. -/
def sine277 : IntervalRat :=
  ⟨(0x34d02bc46830bab6057dee49405d973fa2d5aee09c60c68823a0aa58208d2ad /
    0x4e340ab190473a0fc0f4d68c0000000000000000000000000000000000000000 : ℚ),
   (171730940630239623599663346459020606763846456189959574277121437192992203131 /
    0x8b072f748eb783aa3a96d2c0000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine277_eq :
    IntervalRat.cosComputable input277 10 = cosine277 := by gerver_interval_eq

theorem sine277_eq :
    IntervalRat.sinComputable input277 10 = sine277 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 278. -/
def input278 : IntervalRat :=
  ⟨(13091 /
    256000 : ℚ),
   (55407 /
    1024000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input278` at Taylor depth ten. -/
def cosine278 : IntervalRat :=
  ⟨(58068614488347797257938124556677227670376185409015683835950439247778627 /
    58153724815590069439541558887265075200000000000000000000000000000000000 : ℚ),
   (58077708416158082743788123825135710124108110840820270106605677006941373 /
    58153724815590069439541558887265075200000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input278` at Taylor depth ten. -/
def sine278 : IntervalRat :=
  ⟨(2972339789405153635766521085704333133059058090885661898941823889314627 /
    58153724815590069439541558887265075200000000000000000000000000000000000 : ℚ),
   (3145233737253775122543187398579857815088211742473010288218178670685373 /
    58153724815590069439541558887265075200000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine278_eq :
    IntervalRat.cosComputable input278 10 = cosine278 := by gerver_interval_eq

theorem sine278_eq :
    IntervalRat.sinComputable input278 10 = sine278 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 279. -/
def input279 : IntervalRat :=
  ⟨(55407 /
    1024000 : ℚ),
   (1169 /
    20480 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input279` at Taylor depth ten. -/
def cosine279 : IntervalRat :=
  ⟨(118241324143032891622769150108754702084347295689047249094597 /
    118434214424436004275729209070978701721600000000000000000000 : ℚ),
   (73913056534415266350933754420523536873712051612955153096022987 /
    74021384015272502672330755669361688576000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input279` at Taylor depth ten. -/
def sine279 : IntervalRat :=
  ⟨(6404806328428631975687442930706328207302018931515966915781 /
    118434214424436004275729209070978701721600000000000000000000 : ℚ),
   (270277442876571203663162852333688190034289773905935396979 /
    4737368576977440171029168362839148068864000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine279_eq :
    IntervalRat.cosComputable input279 10 = cosine279 := by gerver_interval_eq

theorem sine279_eq :
    IntervalRat.sinComputable input279 10 = sine279 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 280. -/
def input280 : IntervalRat :=
  ⟨(2737 /
    80000 : ℚ),
   (22287 /
    640000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input280` at Taylor depth ten. -/
def cosine280 : IntervalRat :=
  ⟨(3634017634803156717497237638463771821889193844281576170175727760210177 /
    3636222191809626814545920000000000000000000000000000000000000000000000 : ℚ),
   (3634094316626206112538700628899647356706954850252209604560457993389823 /
    3636222191809626814545920000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input280` at Taylor depth ten. -/
def sine280 : IntervalRat :=
  ⟨(124379109620800622401333688262961909553797338494648789816757023570177 /
    3636222191809626814545920000000000000000000000000000000000000000000000 : ℚ),
   (126601055257965600749051224277942227847822657746844206967370976429823 /
    3636222191809626814545920000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine280_eq :
    IntervalRat.cosComputable input280 10 = cosine280 := by gerver_interval_eq

theorem sine280_eq :
    IntervalRat.sinComputable input280 10 = sine280 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 281. -/
def input281 : IntervalRat :=
  ⟨(22287 /
    640000 : ℚ),
   (11339 /
    320000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input281` at Taylor depth ten. -/
def cosine281 : IntervalRat :=
  ⟨(143725150646765375793945586767007407635924431942236185987895978853261 /
    143815428484658091786240000000000000000000000000000000000000000000000 : ℚ),
   (143728237151111985802018701672707900972256422088990423688259386231739 /
    143815428484658091786240000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input281` at Taylor depth ten. -/
def sine281 : IntervalRat :=
  ⟨(5007099614794532182312283839737240858247947021069698551083437473261 /
    143815428484658091786240000000000000000000000000000000000000000000000 : ℚ),
   (5094979923803061852705575037568239837083917889221551900596562526739 /
    143815428484658091786240000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine281_eq :
    IntervalRat.cosComputable input281 10 = cosine281 := by gerver_interval_eq

theorem sine281_eq :
    IntervalRat.sinComputable input281 10 = sine281 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 282. -/
def input282 : IntervalRat :=
  ⟨(2737 /
    80000 : ℚ),
   (44183 /
    1280000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input282` at Taylor depth ten. -/
def cosine282 : IntervalRat :=
  ⟨(200948768406384323305255868942220773389996210355522635318369549258260494611 /
    201068542318305124337131192320000000000000000000000000000000000000000000000 : ℚ),
   (602852637373375883514215646247170694534997511280780578184420063700254676167 /
    603205626954915373011393576960000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input282` at Taylor depth ten. -/
def sine282 : IntervalRat :=
  ⟨(6877691529115486628279230163156702498298477956006731669113618680709134611 /
    201068542318305124337131192320000000000000000000000000000000000000000000000 : ℚ),
   (6939123775096997441301874141051460731870291670769284850893242119290865389 /
    201068542318305124337131192320000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine282_eq :
    IntervalRat.cosComputable input282 10 = cosine282 := by gerver_interval_eq

theorem sine282_eq :
    IntervalRat.sinComputable input282 10 = sine282 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 283. -/
def input283 : IntervalRat :=
  ⟨(44183 /
    1280000 : ℚ),
   (22287 /
    640000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input283` at Taylor depth ten. -/
def cosine283 : IntervalRat :=
  ⟨(3634017638660435143260682771187317064020420769515724626083808637210177 /
    3636222191809626814545920000000000000000000000000000000000000000000000 : ℚ),
   (3634056149222013558576822913379209852648888171373866933504850016639823 /
    3636222191809626814545920000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input283` at Taylor depth ten. -/
def sine283 : IntervalRat :=
  ⟨(17927091058843063900051356694667679956006393357163707149612146224311 /
    519460313115660973506560000000000000000000000000000000000000000000000 : ℚ),
   (18085801742855083781199151109653549944645843614290506758995853775689 /
    519460313115660973506560000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine283_eq :
    IntervalRat.cosComputable input283 10 = cosine283 := by gerver_interval_eq

theorem sine283_eq :
    IntervalRat.sinComputable input283 10 = sine283 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 284. -/
def input284 : IntervalRat :=
  ⟨(22287 /
    640000 : ℚ),
   (8993 /
    256000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input284` at Taylor depth ten. -/
def cosine284 : IntervalRat :=
  ⟨(8818592542911088215562759565925107816044146876400878191642563471949 /
    8824036600026190599480957468672000000000000000000000000000000000000 : ℚ),
   (1543270193507630176044261553426370656982947797250507998907312173339997 /
    1544206405004583354909167557017600000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input284` at Taylor depth ten. -/
def sine284 : IntervalRat :=
  ⟨(61444018177989757967034151211159262174878489346984528108505332649 /
    1764807320005238119896191493734400000000000000000000000000000000000 : ℚ),
   (433882551086289239220375412679046210093122487951510441416543772257 /
    12353651240036666839273340456140800000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine284_eq :
    IntervalRat.cosComputable input284 10 = cosine284 := by gerver_interval_eq

theorem sine284_eq :
    IntervalRat.sinComputable input284 10 = sine284 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 285. -/
def input285 : IntervalRat :=
  ⟨(8993 /
    256000 : ℚ),
   (11339 /
    320000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input285` at Taylor depth ten. -/
def cosine285 : IntervalRat :=
  ⟨(47908383602510516244004235774486020464477697994080729028633361709837 /
    47938476161552697262080000000000000000000000000000000000000000000000 : ℚ),
   (1149813606155976216788525107000468365683140122941763655816953611542037 /
    1150523427877264734289920000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input285` at Taylor depth ten. -/
def sine285 : IntervalRat :=
  ⟨(1683673847456539907968692881253975806979875172542481135744812491087 /
    47938476161552697262080000000000000000000000000000000000000000000000 : ℚ),
   (188702288005042081286201879121775394212859851143967266653354167657 /
    5326497351283633029120000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine285_eq :
    IntervalRat.cosComputable input285 10 = cosine285 := by gerver_interval_eq

theorem sine285_eq :
    IntervalRat.sinComputable input285 10 = sine285 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 286. -/
def input286 : IntervalRat :=
  ⟨(11339 /
    320000 : ℚ),
   (45747 /
    1280000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input286` at Taylor depth ten. -/
def cosine286 : IntervalRat :=
  ⟨(7442227395079216458211674648737002280083521536909487527018873479251950437 /
    7446983048826115716190044160000000000000000000000000000000000000000000000 : ℚ),
   (7442308349369191556603932107058437902567267302943946570721558210066449563 /
    7446983048826115716190044160000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input286` at Taylor depth ten. -/
def sine286 : IntervalRat :=
  ⟨(263823016413622918387818823031867127252280742763629605991110355929070437 /
    7446983048826115716190044160000000000000000000000000000000000000000000000 : ℚ),
   (266098317193238631618502095828198159399578792032990409306515756070929563 /
    7446983048826115716190044160000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine286_eq :
    IntervalRat.cosComputable input286 10 = cosine286 := by gerver_interval_eq

theorem sine286_eq :
    IntervalRat.sinComputable input286 10 = sine286 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 287. -/
def input287 : IntervalRat :=
  ⟨(45747 /
    1280000 : ℚ),
   (23069 /
    640000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input287` at Taylor depth ten. -/
def cosine287 : IntervalRat :=
  ⟨(294342679111339340985118581458016617968865252296701751577460359190080731 /
    294533997536579771978219520000000000000000000000000000000000000000000000 : ℚ),
   (294345908400062170680301033619728127048913475587729127007347971370089269 /
    294533997536579771978219520000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input287` at Taylor depth ten. -/
def sine287 : IntervalRat :=
  ⟨(10524319723762930992801982652029468376477341029565801815021598836920731 /
    294533997536579771978219520000000000000000000000000000000000000000000000 : ℚ),
   (10614309974633670224408702114559746733952867281476602675056481163079269 /
    294533997536579771978219520000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine287_eq :
    IntervalRat.cosComputable input287 10 = cosine287 := by gerver_interval_eq

theorem sine287_eq :
    IntervalRat.sinComputable input287 10 = sine287 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 288. -/
def input288 : IntervalRat :=
  ⟨(23069 /
    640000 : ℚ),
   (46529 /
    1280000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input288` at Taylor depth ten. -/
def cosine288 : IntervalRat :=
  ⟨(28705101828050784777359413366696467030656379214874526866567099561126059651 /
    28724077474043589191018741760000000000000000000000000000000000000000000000 : ℚ),
   (86116258322598178850758307697286981966519050781461853417513069816231421047 /
    86172232422130767573056225280000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input288` at Taylor depth ten. -/
def sine288 : IntervalRat :=
  ⟨(1035140344588264188292950419459749101457082071962717382001535424288939651 /
    28724077474043589191018741760000000000000000000000000000000000000000000000 : ℚ),
   (1043916568881172577392215221681807450898404450998679158739719743711060349 /
    28724077474043589191018741760000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine288_eq :
    IntervalRat.cosComputable input288 10 = cosine288 := by gerver_interval_eq

theorem sine288_eq :
    IntervalRat.sinComputable input288 10 = sine288 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 289. -/
def input289 : IntervalRat :=
  ⟨(46529 /
    1280000 : ℚ),
   (1173 /
    32000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input289` at Taylor depth ten. -/
def cosine289 : IntervalRat :=
  ⟨(1419445117218504247460339365015776677860604289975476624861 /
    1420399293675635474432000000000000000000000000000000000000 : ℚ),
   (2271137529025999125973147779345819249217024925364657098183509 /
    2272638869881016759091200000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input289` at Taylor depth ten. -/
def sine289 : IntervalRat :=
  ⟨(645263272702907166612919218180837967107059085472059983 /
    17754991170945443430400000000000000000000000000000000000 : ℚ),
   (650688072217380896702615738857707673744632470208669917 /
    17754991170945443430400000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine289_eq :
    IntervalRat.cosComputable input289 10 = cosine289 := by gerver_interval_eq

theorem sine289_eq :
    IntervalRat.sinComputable input289 10 = sine289 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 290. -/
def input290 : IntervalRat :=
  ⟨(1173 /
    40000 : ℚ),
   (37927 /
    1280000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input290` at Taylor depth ten. -/
def cosine290 : IntervalRat :=
  ⟨(602940849313349133609474522009841147996210548370844069156992034152504506377 /
    603205626954915373011393576960000000000000000000000000000000000000000000000 : ℚ),
   (602946280894517360153983450081139249493143338428115249807766723878855493623 /
    603205626954915373011393576960000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input290` at Taylor depth ten. -/
def sine290 : IntervalRat :=
  ⟨(17686416734813088528377846700134343193669155923992786133149844035722426377 /
    603205626954915373011393576960000000000000000000000000000000000000000000000 : ℚ),
   (17870703889232683317049479623653623396324714819351912805757320636277573623 /
    603205626954915373011393576960000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine290_eq :
    IntervalRat.cosComputable input290 10 = cosine290 := by gerver_interval_eq

theorem sine290_eq :
    IntervalRat.sinComputable input290 10 = sine290 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 291. -/
def input291 : IntervalRat :=
  ⟨(37927 /
    1280000 : ℚ),
   (19159 /
    640000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input291` at Taylor depth ten. -/
def cosine291 : IntervalRat :=
  ⟨(14019144397443482802762254249999920028148961837856273015439472514700821 /
    14025428454122846284677120000000000000000000000000000000000000000000000 : ℚ),
   (42057815995551983416847977715049892516777122063221786423327357696207537 /
    42076285362368538854031360000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input291` at Taylor depth ten. -/
def sine291 : IntervalRat :=
  ⟨(415517951183765123469565414876663524283387931860159953657268365540821 /
    14025428454122846284677120000000000000000000000000000000000000000000000 : ℚ),
   (139934304896025572249739768423599623339832439617482211705497211486393 /
    4675142818040948761559040000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine291_eq :
    IntervalRat.cosComputable input291 10 = cosine291 := by gerver_interval_eq

theorem sine291_eq :
    IntervalRat.sinComputable input291 10 = sine291 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 292. -/
def input292 : IntervalRat :=
  ⟨(19159 /
    640000 : ℚ),
   (38709 /
    1280000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input292` at Taylor depth ten. -/
def cosine292 : IntervalRat :=
  ⟨(676688910119300346866645142538630066267816918932594346985240121247001801 /
    676998458984192337835458560000000000000000000000000000000000000000000000 : ℚ),
   (676695132513014881610896682586157644093339190280512944403815612410598199 /
    676998458984192337835458560000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input292` at Taylor depth ten. -/
def sine292 : IntervalRat :=
  ⟨(20263494584982340545256481615008014754078426836411826454673545549081801 /
    676998458984192337835458560000000000000000000000000000000000000000000000 : ℚ),
   (20470327662535631576482295902167338106489371330258945846527862450918199 /
    676998458984192337835458560000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine292_eq :
    IntervalRat.cosComputable input292 10 = cosine292 := by gerver_interval_eq

theorem sine292_eq :
    IntervalRat.sinComputable input292 10 = sine292 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 293. -/
def input293 : IntervalRat :=
  ⟨(38709 /
    1280000 : ℚ),
   (391 /
    12800 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input293` at Taylor depth ten. -/
def cosine293 : IntervalRat :=
  ⟨(942069092698446349429290587841646237096634834562030824603 /
    942508792117055270330302464000000000000000000000000000000 : ℚ),
   (4710389216918914567866468952333679616716187019956137406359189 /
    4712543960585276351651512320000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input293` at Taylor depth ten. -/
def sine293 : IntervalRat :=
  ⟨(814238821863879637858128902918994181241180833306794139 /
    26928822631915864866580070400000000000000000000000000000 : ℚ),
   (32898640088018175072278821057986223326558354738439469 /
    1077152905276634594663202816000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine293_eq :
    IntervalRat.cosComputable input293 10 = cosine293 := by gerver_interval_eq

theorem sine293_eq :
    IntervalRat.sinComputable input293 10 = sine293 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 294. -/
def input294 : IntervalRat :=
  ⟨(1173 /
    40000 : ℚ),
   (19159 /
    640000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input294` at Taylor depth ten. -/
def cosine294 : IntervalRat :=
  ⟨(42057433164036745534500146247848439165169979873868514443562044349102463 /
    42076285362368538854031360000000000000000000000000000000000000000000000 : ℚ),
   (42058194844292893866525020543670607095347810617806923473034058409297537 /
    42076285362368538854031360000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input294` at Taylor depth ten. -/
def sine294 : IntervalRat :=
  ⟨(1233702782730183393273969236143649929220793519224021541503901096622463 /
    42076285362368538854031360000000000000000000000000000000000000000000000 : ℚ),
   (1259412524574567263300792648377735874833370992896929656421474903377537 /
    42076285362368538854031360000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine294_eq :
    IntervalRat.cosComputable input294 10 = cosine294 := by gerver_interval_eq

theorem sine294_eq :
    IntervalRat.sinComputable input294 10 = sine294 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 295. -/
def input295 : IntervalRat :=
  ⟨(19159 /
    640000 : ℚ),
   (391 /
    12800 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input295` at Taylor depth ten. -/
def cosine295 : IntervalRat :=
  ⟨(942069092024858820795200323050681233218982588735158993873 /
    942508792117055270330302464000000000000000000000000000000 : ℚ),
   (65422673989510057101921169261192020477071324372923536732943 /
    65451999452573282661826560000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input295` at Taylor depth ten. -/
def sine295 : IntervalRat :=
  ⟨(1880699770096866681137689127482045403816113189214033087 /
    62833919474470351355353497600000000000000000000000000000 : ℚ),
   (76763728745155018835419204547683866379074829654641001 /
    2513356778978814054214139904000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine295_eq :
    IntervalRat.cosComputable input295 10 = cosine295 := by gerver_interval_eq

theorem sine295_eq :
    IntervalRat.sinComputable input295 10 = sine295 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 296. -/
def input296 : IntervalRat :=
  ⟨(391 /
    12800 : ℚ),
   (39491 /
    1280000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input296` at Taylor depth ten. -/
def cosine296 : IntervalRat :=
  ⟨(28710407784661730943542116093801590245427893153421141260438806228909884529 /
    28724077474043589191018741760000000000000000000000000000000000000000000000 : ℚ),
   (602924220202327528282780214404539437980714669931916318520351661192892424891 /
    603205626954915373011393576960000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input296` at Taylor depth ten. -/
def sine296 : IntervalRat :=
  ⟨(877291610996217811128679963105149500245422040158203571503254228909884529 /
    28724077474043589191018741760000000000000000000000000000000000000000000000 : ℚ),
   (6202471081210638112657659395610571729200917386595739108277220397630808297 /
    201068542318305124337131192320000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine296_eq :
    IntervalRat.cosComputable input296 10 = cosine296 := by gerver_interval_eq

theorem sine296_eq :
    IntervalRat.sinComputable input296 10 = sine296 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 297. -/
def input297 : IntervalRat :=
  ⟨(39491 /
    1280000 : ℚ),
   (19941 /
    640000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input297` at Taylor depth ten. -/
def cosine297 : IntervalRat :=
  ⟨(3634457292688402988529356606783843571191261898501548803899285875619539 /
    3636222191809626814545920000000000000000000000000000000000000000000000 : ℚ),
   (3634491731648707432025233380589422827112618931548542243019439161830461 /
    3636222191809626814545920000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input297` at Taylor depth ten. -/
def sine297 : IntervalRat :=
  ⟨(112167826012386209536701706417868826582264190147408946172948760859539 /
    3636222191809626814545920000000000000000000000000000000000000000000000 : ℚ),
   (113278756228051072907481716203804557357055356393843668204395239140461 /
    3636222191809626814545920000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine297_eq :
    IntervalRat.cosComputable input297 10 = cosine297 := by gerver_interval_eq

theorem sine297_eq :
    IntervalRat.sinComputable input297 10 = sine297 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 298. -/
def input298 : IntervalRat :=
  ⟨(19941 /
    640000 : ℚ),
   (40273 /
    1280000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input298` at Taylor depth ten. -/
def cosine298 : IntervalRat :=
  ⟨(602907083002328376050617887549711301086702984790684729257893535306994183823 /
    603205626954915373011393576960000000000000000000000000000000000000000000000 : ℚ),
   (602912852298391193098756977776233731536874953662250801657278295768169976177 /
    603205626954915373011393576960000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input298` at Taylor depth ten. -/
def sine298 : IntervalRat :=
  ⟨(18791467064431961085982584934481863812932850212744492790259038594679303823 /
    603205626954915373011393576960000000000000000000000000000000000000000000000 : ℚ),
   (18975757640685885301738381063264242323244160751916519151613068925320696177 /
    603205626954915373011393576960000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine298_eq :
    IntervalRat.cosComputable input298 10 = cosine298 := by gerver_interval_eq

theorem sine298_eq :
    IntervalRat.sinComputable input298 10 = sine298 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 299. -/
def input299 : IntervalRat :=
  ⟨(40273 /
    1280000 : ℚ),
   (5083 /
    160000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input299` at Taylor depth ten. -/
def cosine299 : IntervalRat :=
  ⟨(374330368127013072135692997999729337668420576853400950271614745951 /
    374519345012130447360000000000000000000000000000000000000000000000 : ℚ),
   (71872125143863487185827284953162508590157025776312144622458488980533 /
    71907714242329045893120000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input299` at Taylor depth ten. -/
def sine299 : IntervalRat :=
  ⟨(736351592249045229206141876031624688443386222993232986645135411 /
    23407459063258152960000000000000000000000000000000000000000000000 : ℚ),
   (743503030739862984027393278785599930079194885947028396237677089 /
    23407459063258152960000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine299_eq :
    IntervalRat.cosComputable input299 10 = cosine299 := by gerver_interval_eq

theorem sine299_eq :
    IntervalRat.sinComputable input299 10 = sine299 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 300. -/
def input300 : IntervalRat :=
  ⟨(391 /
    12800 : ℚ),
   (19941 /
    640000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input300` at Taylor depth ten. -/
def cosine300 : IntervalRat :=
  ⟨(3634457289929803384421228205989848582569787635352210878814900760859539 /
    3636222191809626814545920000000000000000000000000000000000000000000000 : ℚ),
   (3634525828550307283260636279786861284042015073043259332261099239140461 /
    3636222191809626814545920000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input300` at Taylor depth ten. -/
def sine300 : IntervalRat :=
  ⟨(111057253460756633176482403521466861808446063624429357738900760859539 /
    3636222191809626814545920000000000000000000000000000000000000000000000 : ℚ),
   (113279110367799632004355118473853123126221309898540242261099239140461 /
    3636222191809626814545920000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine300_eq :
    IntervalRat.cosComputable input300 10 = cosine300 := by gerver_interval_eq

theorem sine300_eq :
    IntervalRat.sinComputable input300 10 = sine300 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 301. -/
def input301 : IntervalRat :=
  ⟨(19941 /
    640000 : ℚ),
   (5083 /
    160000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input301` at Taylor depth ten. -/
def cosine301 : IntervalRat :=
  ⟨(35093471983664700241529836858671166425119214502914292360655578429 /
    35111188594887229440000000000000000000000000000000000000000000000 : ℚ),
   (1123012700620424039868017832810437874949271640909885100623218268397 /
    1123558035036391342080000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input301` at Taylor depth ten. -/
def sine301 : IntervalRat :=
  ⟨(2187607642640312505726006702726360030965673657101741018599468733 /
    70222377189774458880000000000000000000000000000000000000000000000 : ℚ),
   (2230516204189740708162532499503776718280406556978902892150531267 /
    70222377189774458880000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine301_eq :
    IntervalRat.cosComputable input301 10 = cosine301 := by gerver_interval_eq

theorem sine301_eq :
    IntervalRat.sinComputable input301 10 = sine301 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 302. -/
def input302 : IntervalRat :=
  ⟨(41837 /
    1280000 : ℚ),
   (16813 /
    512000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input302` at Taylor depth ten. -/
def cosine302 : IntervalRat :=
  ⟨(126433189834487527231119001735909721457496316272420232640924461832789911 /
    126501388697975468434159006270881792000000000000000000000000000000000000 : ℚ),
   (1053615190195877737014266943399260813674916188377490128684232469258724203 /
    1054178239149795570284658385590681600000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input302` at Taylor depth ten. -/
def sine302 : IntervalRat :=
  ⟨(91866102195662315592475275846085353998554252036161528981843388577107 /
    2811141971066121520759089028241817600000000000000000000000000000000000 : ℚ),
   (276886611052778309453620468615733566419429987148126943812607569027079 /
    8433425913198364562277267084725452800000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine302_eq :
    IntervalRat.cosComputable input302 10 = cosine302 := by gerver_interval_eq

theorem sine302_eq :
    IntervalRat.sinComputable input302 10 = sine302 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 303. -/
def input303 : IntervalRat :=
  ⟨(16813 /
    512000 : ℚ),
   (10557 /
    320000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input303` at Taylor depth ten. -/
def cosine303 : IntervalRat :=
  ⟨(14196263950906838306208829547643962458926700749322305191506616942501 /
    14203992936756354744320000000000000000000000000000000000000000000000 : ℚ),
   (908565462806283188650698499388740816713339281719790748811482042633061 /
    909055547952406703636480000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input303` at Taylor depth ten. -/
def sine303 : IntervalRat :=
  ⟨(58293070282139230949047082937327134058408209201529291223359295547 /
    1775499117094544343040000000000000000000000000000000000000000000000 : ℚ),
   (58564298996179945660797862293875758355528294962724900397734454453 /
    1775499117094544343040000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine303_eq :
    IntervalRat.cosComputable input303 10 = cosine303 := by gerver_interval_eq

theorem sine303_eq :
    IntervalRat.sinComputable input303 10 = sine303 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 304. -/
def input304 : IntervalRat :=
  ⟨(5083 /
    160000 : ℚ),
   (8211 /
    256000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input304` at Taylor depth ten. -/
def cosine304 : IntervalRat :=
  ⟨(108882692513881704155307869705643632853464323462823132197854741151 /
    108938723457113464191122931712000000000000000000000000000000000000 : ℚ),
   (2722093869427815278834903278714391142585467711082596620360536440441 /
    2723468086427836604778073292800000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input304` at Taylor depth ten. -/
def sine304 : IntervalRat :=
  ⟨(692050741304742608211729959492263980725358942153295738893258067 /
    21787744691422692838224586342400000000000000000000000000000000000 : ℚ),
   (698707346773295218107284121301218278016452455797394695746204333 /
    21787744691422692838224586342400000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine304_eq :
    IntervalRat.cosComputable input304 10 = cosine304 := by gerver_interval_eq

theorem sine304_eq :
    IntervalRat.sinComputable input304 10 = sine304 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 305. -/
def input305 : IntervalRat :=
  ⟨(8211 /
    256000 : ℚ),
   (20723 /
    640000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input305` at Taylor depth ten. -/
def cosine305 : IntervalRat :=
  ⟨(294379609547674535087178690762963725702361743972848302898400822776358773 /
    294533997536579771978219520000000000000000000000000000000000000000000000 : ℚ),
   (294382509036693332467122167599834902755540111102561124856755903279891227 /
    294533997536579771978219520000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input305` at Taylor depth ten. -/
def sine305 : IntervalRat :=
  ⟨(9445297184985712283363132807511523407826831224425816688874001251358773 /
    294533997536579771978219520000000000000000000000000000000000000000000000 : ℚ),
   (9535283691120683030775532207700826973193763117416329294405998748641227 /
    294533997536579771978219520000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine305_eq :
    IntervalRat.cosComputable input305 10 = cosine305 := by gerver_interval_eq

theorem sine305_eq :
    IntervalRat.sinComputable input305 10 = sine305 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 306. -/
def input306 : IntervalRat :=
  ⟨(20723 /
    640000 : ℚ),
   (41837 /
    1280000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input306` at Taylor depth ten. -/
def cosine306 : IntervalRat :=
  ⟨(200961148985609777652919651471219722595403238586404444347424636319305283129 /
    201068542318305124337131192320000000000000000000000000000000000000000000000 : ℚ),
   (602889441396155786069759741014564279745035804481179431500859894432343350613 /
    603205626954915373011393576960000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input306` at Taylor depth ten. -/
def sine306 : IntervalRat :=
  ⟨(929911057855128232773624690074946690910026639154783959800442616192960447 /
    28724077474043589191018741760000000000000000000000000000000000000000000000 : ℚ),
   (312895637890341430418412959754638220912831101851504674975658071935679851 /
    9574692491347863063672913920000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine306_eq :
    IntervalRat.cosComputable input306 10 = cosine306 := by gerver_interval_eq

theorem sine306_eq :
    IntervalRat.sinComputable input306 10 = sine306 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 307. -/
def input307 : IntervalRat :=
  ⟨(41837 /
    1280000 : ℚ),
   (10557 /
    320000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input307` at Taylor depth ten. -/
def cosine307 : IntervalRat :=
  ⟨(253504713293942186273010201394546045877966424060615632086119245971 /
    253642731013506334720000000000000000000000000000000000000000000000 : ℚ),
   (14196406423995675531478633632984890304416347056151273541193139523749 /
    14203992936756354744320000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input307` at Taylor depth ten. -/
def sine307 : IntervalRat :=
  ⟨(8288848531060013006629407436239236485245068163935160730430792221 /
    253642731013506334720000000000000000000000000000000000000000000000 : ℚ),
   (58564396689978560137010325478442708602418660668251344801984454453 /
    1775499117094544343040000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine307_eq :
    IntervalRat.cosComputable input307 10 = cosine307 := by gerver_interval_eq

theorem sine307_eq :
    IntervalRat.sinComputable input307 10 = sine307 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 308. -/
def input308 : IntervalRat :=
  ⟨(10557 /
    320000 : ℚ),
   (84847 /
    2560000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input308` at Taylor depth ten. -/
def cosine308 : IntervalRat :=
  ⟨(0x185f5b2e4fc30a8affcd1ddeed4ae3165cda411c90e77dae7d8aa895355537f07 /
    0x1862c8df62440c948dfbedc90e3c7300000000000000000000000000000000000 : ℚ),
   (0x185f6340982bfb4a3e6bf587d549c90605444ecbbb7c57790437dacbbedac80f9 /
    0x1862c8df62440c948dfbedc90e3c7300000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input308` at Taylor depth ten. -/
def sine308 : IntervalRat :=
  ⟨(0xcdea68eef8ec60ed7aa9b7b3ac5e70d75add1a311c6de3948bd2e72d2537f07 /
    0x1862c8df62440c948dfbedc90e3c7300000000000000000000000000000000000 : ℚ),
   (0xcede8c195791cf6bee6afba655ef4e8056afb146b9e626c5555e46d2dac80f9 /
    0x1862c8df62440c948dfbedc90e3c7300000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine308_eq :
    IntervalRat.cosComputable input308 10 = cosine308 := by gerver_interval_eq

theorem sine308_eq :
    IntervalRat.sinComputable input308 10 = sine308 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 309. -/
def input309 : IntervalRat :=
  ⟨(84847 /
    2560000 : ℚ),
   (42619 /
    1280000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input309` at Taylor depth ten. -/
def cosine309 : IntervalRat :=
  ⟨(602871291677118476111164426091735136426259344473530842685240890532937673181 /
    603205626954915373011393576960000000000000000000000000000000000000000000000 : ℚ),
   (7442893237263268079265702292635177928662593811345901909723534044308674899 /
    7446983048826115716190044160000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input309` at Taylor depth ten. -/
def sine309 : IntervalRat :=
  ⟨(2220951896797956715739055232813209997278458736737492568149612240633705909 /
    67022847439435041445710397440000000000000000000000000000000000000000000000 : ℚ),
   (6693571417171149001610691851749328635759314661199018157531141518098882273 /
    201068542318305124337131192320000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine309_eq :
    IntervalRat.cosComputable input309 10 = cosine309 := by gerver_interval_eq

theorem sine309_eq :
    IntervalRat.sinComputable input309 10 = sine309 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 310. -/
def input310 : IntervalRat :=
  ⟨(42619 /
    1280000 : ℚ),
   (85629 /
    2560000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input310` at Taylor depth ten. -/
def cosine310 : IntervalRat :=
  ⟨(0x21b32b8e729bfacfbe6f718258d7e750880968296cd0dc3d7c0e51f006b6550b /
    0x21b7ffa0554e4a48ab0a2c585f89500000000000000000000000000000000000 : ℚ),
   (0x4d0758bb40f73915a762f0c03d6a599348f13147f37cd603ad117851f118623 /
    0x4d124849e78e60a6193bd313238300000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input310` at Taylor depth ten. -/
def sine310 : IntervalRat :=
  ⟨(507718065950176322728762862005980452335106005240120344963497451303858689291 /
    0x21b7ffa0554e4a48ab0a2c585f89500000000000000000000000000000000000 : ℚ),
   (510047914656362523362125366047896810379025558444161941958694674648141310709 /
    0x21b7ffa0554e4a48ab0a2c585f89500000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine310_eq :
    IntervalRat.cosComputable input310 10 = cosine310 := by gerver_interval_eq

theorem sine310_eq :
    IntervalRat.sinComputable input310 10 = sine310 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 311. -/
def input311 : IntervalRat :=
  ⟨(85629 /
    2560000 : ℚ),
   (4301 /
    128000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input311` at Taylor depth ten. -/
def cosine311 : IntervalRat :=
  ⟨(2740296043280635844824217881792273820169324059181578732609620321 /
    2741843758885978968233607168000000000000000000000000000000000000 : ℚ),
   (274031008275388253357506149049768043083391723109225728375007404579 /
    274184375888597896823360716800000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input311` at Taylor depth ten. -/
def sine311 : IntervalRat :=
  ⟨(18338840713713805880311103251150314681017045942177770031425409 /
    548368751777195793646721433600000000000000000000000000000000000 : ℚ),
   (2631801594612716805241312441391778015672779450855051546643913 /
    78338393111027970520960204800000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine311_eq :
    IntervalRat.cosComputable input311 10 = cosine311 := by gerver_interval_eq

theorem sine311_eq :
    IntervalRat.sinComputable input311 10 = sine311 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 312. -/
def input312 : IntervalRat :=
  ⟨(4301 /
    128000 : ℚ),
   (86411 /
    2560000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input312` at Taylor depth ten. -/
def cosine312 : IntervalRat :=
  ⟨(0xaa9a99b3048f5c9ba313b52ff334d8bc371963faf4998876d2521cb10962d3a2d /
    0xaab37e1bafdc580fe1e3807f63a72500000000000000000000000000000000000 : ℚ),
   (0x81fc0ea9518fb3f4e58aac02a76c1babcf779ce5e326da72d1f06b0ee907c047 /
    0x820ed9fcb6c043184a94f4304bed100000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input312` at Taylor depth ten. -/
def sine312 : IntervalRat :=
  ⟨(0xa31f12baa90fc0f56cfc3220115f18f007111ffabd01149689e27a837edea05 /
    0x12f77fca2ffc09c8e035b8f1b5bd3d00000000000000000000000000000000000 : ℚ),
   (0xa3dcf58583ea8572270c9f1734acef2b6ca18d376f07677c503fcd9c81215fb /
    0x12f77fca2ffc09c8e035b8f1b5bd3d00000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine312_eq :
    IntervalRat.cosComputable input312 10 = cosine312 := by gerver_interval_eq

theorem sine312_eq :
    IntervalRat.sinComputable input312 10 = sine312 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 313. -/
def input313 : IntervalRat :=
  ⟨(86411 /
    2560000 : ℚ),
   (43401 /
    1280000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input313` at Taylor depth ten. -/
def cosine313 : IntervalRat :=
  ⟨(7442702606323142143460711541552615570670754955221401423246336180118020279 /
    7446983048826115716190044160000000000000000000000000000000000000000000000 : ℚ),
   (7442741085669096745161390453398520486543004938928438525260527957294479721 /
    7446983048826115716190044160000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input313` at Taylor depth ten. -/
def sine313 : IntervalRat :=
  ⟨(251319513715012463580886678040301008217656822679038522846674185027700279 /
    7446983048826115716190044160000000000000000000000000000000000000000000000 : ℚ),
   (252457140991558001019267491184113599263757298860782552455020790972299721 /
    7446983048826115716190044160000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine313_eq :
    IntervalRat.cosComputable input313 10 = cosine313 := by gerver_interval_eq

theorem sine313_eq :
    IntervalRat.sinComputable input313 10 = sine313 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 314. -/
def input314 : IntervalRat :=
  ⟨(43401 /
    1280000 : ℚ),
   (87193 /
    2560000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input314` at Taylor depth ten. -/
def cosine314 : IntervalRat :=
  ⟨(0xaa9a25d9d015c018f567ff95df7b24eafd8252c7e9b0d48356603ba2dcd3c6bb7 /
    0xaab37e1bafdc580fe1e3807f63a72500000000000000000000000000000000000 : ℚ),
   (0xaa9a5feaa46257054d5c4186ff4cbc0a05da99fec4fd6170431e1cabfa56c9449 /
    0xaab37e1bafdc580fe1e3807f63a72500000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input314` at Taylor depth ten. -/
def sine314 : IntervalRat :=
  ⟨(0x5c96f001c0d7e746db2c1365d818e78a1b045eb1c149fa3bf7f1eb449f676bb7 /
    0xaab37e1bafdc580fe1e3807f63a72500000000000000000000000000000000000 : ℚ),
   (0x5d01bfabf86ab154cd366eef6032d7944ac27536a78c220538185cef00989449 /
    0xaab37e1bafdc580fe1e3807f63a72500000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine314_eq :
    IntervalRat.cosComputable input314 10 = cosine314 := by gerver_interval_eq

theorem sine314_eq :
    IntervalRat.sinComputable input314 10 = sine314 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 315. -/
def input315 : IntervalRat :=
  ⟨(87193 /
    2560000 : ℚ),
   (2737 /
    80000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input315` at Taylor depth ten. -/
def cosine315 : IntervalRat :=
  ⟨(40103590677958067846083041239474030745593831052536904168118181747 /
    40127072679871119360000000000000000000000000000000000000000000000 : ℚ),
   (13688763696101317758729401048718653611541863784418372945305522887649 /
    13696707474729342074880000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input315` at Taylor depth ten. -/
def sine315 : IntervalRat :=
  ⟨(18978501155885874262306797795255685136987633221387429144658401 /
    557320453887098880000000000000000000000000000000000000000000000 : ℚ),
   (1787216219974521324165745283260990678480203455268778147021771 /
    52248792551915520000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine315_eq :
    IntervalRat.cosComputable input315 10 = cosine315 := by gerver_interval_eq

theorem sine315_eq :
    IntervalRat.sinComputable input315 10 = sine315 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 316. -/
def input316 : IntervalRat :=
  ⟨(10557 /
    320000 : ℚ),
   (42619 /
    1280000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input316` at Taylor depth ten. -/
def cosine316 : IntervalRat :=
  ⟨(602871291395678266467430716277122770574854285047707877481103403422284473181 /
    603205626954915373011393576960000000000000000000000000000000000000000000000 : ℚ),
   (602877398406636731335526106244504757638185401555502177392186278048793926819 /
    603205626954915373011393576960000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input316` at Taylor depth ten. -/
def sine316 : IntervalRat :=
  ⟨(19896453857015020477340798324793166304745837764088016709420360533703353181 /
    603205626954915373011393576960000000000000000000000000000000000000000000000 : ℚ),
   (20080748061486683366338259815342104225716806508651232697006644394296646819 /
    603205626954915373011393576960000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine316_eq :
    IntervalRat.cosComputable input316 10 = cosine316 := by gerver_interval_eq

theorem sine316_eq :
    IntervalRat.sinComputable input316 10 = sine316 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 317. -/
def input317 : IntervalRat :=
  ⟨(42619 /
    1280000 : ℚ),
   (4301 /
    128000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input317` at Taylor depth ten. -/
def cosine317 : IntervalRat :=
  ⟨(913432013988582289852669703966517548798454739408867275569778967 /
    913947919628659656077869056000000000000000000000000000000000000 : ℚ),
   (68508101423777140197610703772166814717396750757345575410476248179 /
    68546093972149474205840179200000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input317` at Taylor depth ten. -/
def sine317 : IntervalRat :=
  ⟨(6085033904423267760566224747860914559884853032481637542319403 /
    182789583925731931215573811200000000000000000000000000000000000 : ℚ),
   (6140880822374837581295803015142170576241425433219003148675797 /
    182789583925731931215573811200000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine317_eq :
    IntervalRat.cosComputable input317 10 = cosine317 := by gerver_interval_eq

theorem sine317_eq :
    IntervalRat.sinComputable input317 10 = sine317 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 318. -/
def input318 : IntervalRat :=
  ⟨(4301 /
    128000 : ℚ),
   (43401 /
    1280000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input318` at Taylor depth ten. -/
def cosine318 : IntervalRat :=
  ⟨(7442702602653327010461007724034300756834337961640743648133453436227700279 /
    7446983048826115716190044160000000000000000000000000000000000000000000000 : ℚ),
   (7442779387623581525918700490813763698257690155628795866880738806972299721 /
    7446983048826115716190044160000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input318` at Taylor depth ten. -/
def sine318 : IntervalRat :=
  ⟨(250182321320598701421170981004398783915273081746664845453429513027700279 /
    7446983048826115716190044160000000000000000000000000000000000000000000000 : ℚ),
   (252457573910003733348106684154115265922311467604047112624010486972299721 /
    7446983048826115716190044160000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine318_eq :
    IntervalRat.cosComputable input318 10 = cosine318 := by gerver_interval_eq

theorem sine318_eq :
    IntervalRat.sinComputable input318 10 = sine318 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 319. -/
def input319 : IntervalRat :=
  ⟨(43401 /
    1280000 : ℚ),
   (2737 /
    80000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input319` at Taylor depth ten. -/
def cosine319 : IntervalRat :=
  ⟨(2506474416102704364584466514470165872937162460175285725413106867 /
    2507942042491944960000000000000000000000000000000000000000000000 : ℚ),
   (641664130359918052697435245155937896805660724478460754387998113923 /
    642033162877937909760000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input319` at Taylor depth ten. -/
def sine319 : IntervalRat :=
  ⟨(5313767559644029313520679555371358269758288098130523594090937 /
    156746377655746560000000000000000000000000000000000000000000000 : ℚ),
   (335103621100039945209659296444860466651441412098698211526543 /
    9796648603484160000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine319_eq :
    IntervalRat.cosComputable input319 10 = cosine319 := by gerver_interval_eq

theorem sine319_eq :
    IntervalRat.sinComputable input319 10 = sine319 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 320. -/
def input320 : IntervalRat :=
  ⟨(5083 /
    160000 : ℚ),
   (20723 /
    640000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input320` at Taylor depth ten. -/
def cosine320 : IntervalRat :=
  ⟨(42054229899536452829844736600152002454206785360374549753189280388685539 /
    42076285362368538854031360000000000000000000000000000000000000000000000 : ℚ),
   (98128460263828067240339840420678013389182421301772212517440409433760409 /
    98177999178859923992739840000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input320` at Taylor depth ten. -/
def sine320 : IntervalRat :=
  ⟨(3118447324035279745060922788114448575250370667814114971858224417119591 /
    98177999178859923992739840000000000000000000000000000000000000000000000 : ℚ),
   (3178438229237158722163351230139965788841502971095372519459535582880409 /
    98177999178859923992739840000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine320_eq :
    IntervalRat.cosComputable input320 10 = cosine320 := by gerver_interval_eq

theorem sine320_eq :
    IntervalRat.sinComputable input320 10 = sine320 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 321. -/
def input321 : IntervalRat :=
  ⟨(20723 /
    640000 : ℚ),
   (10557 /
    320000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input321` at Taylor depth ten. -/
def cosine321 : IntervalRat :=
  ⟨(1774532991457345698629680410354317431433806267650481173121963965547 /
    1775499117094544343040000000000000000000000000000000000000000000000 : ℚ),
   (1774568445667194037354484018736949680468442391114909876268401159453 /
    1775499117094544343040000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input321` at Taylor depth ten. -/
def sine321 : IntervalRat :=
  ⟨(57479678588202473827095378723428728330412307808624918202015545547 /
    1775499117094544343040000000000000000000000000000000000000000000000 : ℚ),
   (58564590711228947807926522563648578657966648731627373861984454453 /
    1775499117094544343040000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine321_eq :
    IntervalRat.cosComputable input321 10 = cosine321 := by gerver_interval_eq

theorem sine321_eq :
    IntervalRat.sinComputable input321 10 = sine321 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 322. -/
def input322 : IntervalRat :=
  ⟨(10557 /
    320000 : ℚ),
   (4301 /
    128000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input322` at Taylor depth ten. -/
def cosine322 : IntervalRat :=
  ⟨(2740296039354022314620439814152242606202939437725496131624451461 /
    2741843758885978968233607168000000000000000000000000000000000000 : ℚ),
   (68508795337002032092886189113004645234019924771682836505707396611 /
    68546093972149474205840179200000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input322` at Taylor depth ten. -/
def sine322 : IntervalRat :=
  ⟨(18087623712453821470044296931009284905847102035714303997607809 /
    548368751777195793646721433600000000000000000000000000000000000 : ℚ),
   (18422704646980825423819754404997697689279104023705161366667391 /
    548368751777195793646721433600000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine322_eq :
    IntervalRat.cosComputable input322 10 = cosine322 := by gerver_interval_eq

theorem sine322_eq :
    IntervalRat.sinComputable input322 10 = sine322 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 323. -/
def input323 : IntervalRat :=
  ⟨(4301 /
    128000 : ℚ),
   (2737 /
    80000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input323` at Taylor depth ten. -/
def cosine323 : IntervalRat :=
  ⟨(156654650848779614053498956103380753125203693918001076241747187 /
    156746377655746560000000000000000000000000000000000000000000000 : ℚ),
   (3342035154390595042915511047522201354075710447483044478903533969 /
    3343922723322593280000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input323` at Taylor depth ten. -/
def sine323 : IntervalRat :=
  ⟨(27426540514416763221480190286358870435123702730851436637111 /
    816387383623680000000000000000000000000000000000000000000000 : ℚ),
   (2068547981428438834207331950783662452496499018261899875839 /
    60473139527680000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine323_eq :
    IntervalRat.cosComputable input323 10 = cosine323 := by gerver_interval_eq

theorem sine323_eq :
    IntervalRat.sinComputable input323 10 = sine323 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 324. -/
def input324 : IntervalRat :=
  ⟨(2737 /
    80000 : ℚ),
   (3519 /
    102400 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input324` at Taylor depth ten. -/
def cosine324 : IntervalRat :=
  ⟨(99892700328598876417800315791441946594837817894826050953712713209 /
    99951714526795431849212054337486848000000000000000000000000000000 : ℚ),
   (62433264865372196494336755498661445515326019267597789037949340726039 /
    62469821579247144905757533960929280000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input324` at Taylor depth ten. -/
def sine324 : IntervalRat :=
  ⟨(683784999847312080233825662357886266214326169076372297344289893 /
    19990342905359086369842410867497369600000000000000000000000000000 : ℚ),
   (27473552427985518443523045870223735385063324818825321371383763 /
    799613716214363454793696434699894784000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine324_eq :
    IntervalRat.cosComputable input324 10 = cosine324 := by gerver_interval_eq

theorem sine324_eq :
    IntervalRat.sinComputable input324 10 = sine324 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 325. -/
def input325 : IntervalRat :=
  ⟨(3519 /
    102400 : ℚ),
   (44183 /
    1280000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input325` at Taylor depth ten. -/
def cosine325 : IntervalRat :=
  ⟨(602846305532804407112780740980957214726733859292684376399317327070377403833 /
    603205626954915373011393576960000000000000000000000000000000000000000000000 : ℚ),
   (86121354092234698322947172476068157444742628300922791700003915517847870881 /
    86172232422130767573056225280000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input325` at Taylor depth ten. -/
def sine325 : IntervalRat :=
  ⟨(20725186529624307787003837851010678471992268128102339261663943914127403833 /
    603205626954915373011393576960000000000000000000000000000000000000000000000 : ℚ),
   (20817334979559156137394650839576183877942665434859504656536056085872596167 /
    603205626954915373011393576960000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine325_eq :
    IntervalRat.cosComputable input325 10 = cosine325 := by gerver_interval_eq

theorem sine325_eq :
    IntervalRat.sinComputable input325 10 = sine325 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 326. -/
def input326 : IntervalRat :=
  ⟨(44183 /
    1280000 : ℚ),
   (88757 /
    2560000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input326` at Taylor depth ten. -/
def cosine326 : IntervalRat :=
  ⟨(0xaa993b062b7dfe2fa1b731e4f075809354be4c694ba7881d2a9cd30cffe6bbd13 /
    0xaab37e1bafdc580fe1e3807f63a72500000000000000000000000000000000000 : ℚ),
   (0x12f49b59230bb2b35ab24b796f010652dea9130296d6e9702e959166e60a25cc5 /
    0x12f77fca2ffc09c8e035b8f1b5bd3d00000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input326` at Taylor depth ten. -/
def sine326 : IntervalRat :=
  ⟨(0xa7918234fdd5bb32a15de48614979fe4eb55109736e30eb3f623c6c13d1a33b /
    0x12f77fca2ffc09c8e035b8f1b5bd3d00000000000000000000000000000000000 : ℚ),
   (0x482206ee667fc6804befe9fa2d2e1b7570f3e551cfc848af7023f0817819579 /
    0x820ed9fcb6c043184a94f4304bed100000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine326_eq :
    IntervalRat.cosComputable input326 10 = cosine326 := by gerver_interval_eq

theorem sine326_eq :
    IntervalRat.sinComputable input326 10 = sine326 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 327. -/
def input327 : IntervalRat :=
  ⟨(88757 /
    2560000 : ℚ),
   (22287 /
    640000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input327` at Taylor depth ten. -/
def cosine327 : IntervalRat :=
  ⟨(3634017640601931950939183904859591155823487768911145798014099541622677 /
    3636222191809626814545920000000000000000000000000000000000000000000000 : ℚ),
   (2076592536168705484054083344942132910994779573874413695902890769329631 /
    2077841252462643894026240000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input327` at Taylor depth ten. -/
def sine327 : IntervalRat :=
  ⟨(126044901307717760893871558886165443660447994957280952037969023570177 /
    3636222191809626814545920000000000000000000000000000000000000000000000 : ℚ),
   (126600389194135635785329882132123870489544771388454642935450976429823 /
    3636222191809626814545920000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine327_eq :
    IntervalRat.cosComputable input327 10 = cosine327 := by gerver_interval_eq

theorem sine327_eq :
    IntervalRat.sinComputable input327 10 = sine327 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 328. -/
def input328 : IntervalRat :=
  ⟨(22287 /
    640000 : ℚ),
   (89539 /
    2560000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input328` at Taylor depth ten. -/
def cosine328 : IntervalRat :=
  ⟨(0xaa98c40bbccea6b130b4f574b59182a06971857b6e700cb4001913f08ca1cb2c5 /
    0xaab37e1bafdc580fe1e3807f63a72500000000000000000000000000000000000 : ℚ),
   (0xaa98ffad6a894cc064d4e8338572cb724a7f05b581ea79779e7ba9dcff4b34d3b /
    0xaab37e1bafdc580fe1e3807f63a72500000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input328` at Taylor depth ten. -/
def sine328 : IntervalRat :=
  ⟨(0x5f174cfe7ea4cf79042f11e17a253983c0af2b95df77f6234329f97ee04cb2c5 /
    0xaab37e1bafdc580fe1e3807f63a72500000000000000000000000000000000000 : ℚ),
   (0x5f821cf25a196e44103c75a68743f49f4a9bb651ae2c633d862dd6f31fb34d3b /
    0xaab37e1bafdc580fe1e3807f63a72500000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine328_eq :
    IntervalRat.cosComputable input328 10 = cosine328 := by gerver_interval_eq

theorem sine328_eq :
    IntervalRat.sinComputable input328 10 = sine328 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 329. -/
def input329 : IntervalRat :=
  ⟨(89539 /
    2560000 : ℚ),
   (8993 /
    256000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input329` at Taylor depth ten. -/
def cosine329 : IntervalRat :=
  ⟨(61730147834235147776362644684267880354785463906027659221407157324443 /
    61768256200183334196366702280704000000000000000000000000000000000000 : ℚ),
   (514420654372144923838802440722545124347739047963168572956338621905151 /
    514735468334861118303055852339200000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input329` at Taylor depth ten. -/
def sine329 : IntervalRat :=
  ⟨(47999396271987171025359542878357714218860108500068835297093185127 /
    1372627915559629648808148939571200000000000000000000000000000000000 : ℚ),
   (48209086672836998787277307252098641600161044559477280498692952473 /
    1372627915559629648808148939571200000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine329_eq :
    IntervalRat.cosComputable input329 10 = cosine329 := by gerver_interval_eq

theorem sine329_eq :
    IntervalRat.sinComputable input329 10 = sine329 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 330. -/
def input330 : IntervalRat :=
  ⟨(8993 /
    256000 : ℚ),
   (90321 /
    2560000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input330` at Taylor depth ten. -/
def cosine330 : IntervalRat :=
  ⟨(197947140519658769512235639847514808785383196391654941723563703077017131867 /
    198070406285660843983859875840000000000000000000000000000000000000000000000 : ℚ),
   (197948205555217980791291944970070367850527167471669462386182100110182868133 /
    198070406285660843983859875840000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input330` at Taylor depth ten. -/
def sine330 : IntervalRat :=
  ⟨(6956553276752899156257654086560704338805509255927643537709081969817131867 /
    198070406285660843983859875840000000000000000000000000000000000000000000000 : ℚ),
   (6986811685965455388488630020511403161494776333924709723367398030182868133 /
    198070406285660843983859875840000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine330_eq :
    IntervalRat.cosComputable input330 10 = cosine330 := by gerver_interval_eq

theorem sine330_eq :
    IntervalRat.sinComputable input330 10 = sine330 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 331. -/
def input331 : IntervalRat :=
  ⟨(90321 /
    2560000 : ℚ),
   (11339 /
    320000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input331` at Taylor depth ten. -/
def cosine331 : IntervalRat :=
  ⟨(1149801207107529295762025401182137668305482622140605513515039230504213 /
    1150523427877264734289920000000000000000000000000000000000000000000000 : ℚ),
   (73587674903998435774081983404202881190070586436371649272023517163333493 /
    73633499384144942994554880000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input331` at Taylor depth ten. -/
def sine331 : IntervalRat :=
  ⟨(5072982506168245329142507385962899097342171735565624331929781223261 /
    143815428484658091786240000000000000000000000000000000000000000000000 : ℚ),
   (5094952642867082559308250071489250295318747761290061226942812526739 /
    143815428484658091786240000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine331_eq :
    IntervalRat.cosComputable input331 10 = cosine331 := by gerver_interval_eq

theorem sine331_eq :
    IntervalRat.sinComputable input331 10 = sine331 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 332. -/
def input332 : IntervalRat :=
  ⟨(45747 /
    1280000 : ℚ),
   (18377 /
    512000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input332` at Taylor depth ten. -/
def cosine332 : IntervalRat :=
  ⟨(126419912946022423427048673280905544800514481982845771465406477424232771 /
    126501388697975468434159006270881792000000000000000000000000000000000000 : ℚ),
   (451502160553557904045043009532485624776402704682211880986707947467295907 /
    451790673921340958693425022396006400000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input332` at Taylor depth ten. -/
def sine332 : IntervalRat :=
  ⟨(904033836269155581008949451986950256605564212346013426002571149135527 /
    25300277739595093686831801254176358400000000000000000000000000000000000 : ℚ),
   (907898884597583618148741818301666746704170245313598357585915376611673 /
    25300277739595093686831801254176358400000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine332_eq :
    IntervalRat.cosComputable input332 10 = cosine332 := by gerver_interval_eq

theorem sine332_eq :
    IntervalRat.sinComputable input332 10 = sine332 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 333. -/
def input333 : IntervalRat :=
  ⟨(18377 /
    512000 : ℚ),
   (23069 /
    640000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input333` at Taylor depth ten. -/
def cosine333 : IntervalRat :=
  ⟨(294342679285780674836424391262084248926198617805053564878886188257233231 /
    294533997536579771978219520000000000000000000000000000000000000000000000 : ℚ),
   (130819687718024750444659078131983116450239099717161430668258787963321689 /
    130903998905146565323653120000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input333` at Taylor depth ten. -/
def sine333 : IntervalRat :=
  ⟨(1174366161147822503213025618509336991532027137768345944828724759657859 /
    32725999726286641330913280000000000000000000000000000000000000000000000 : ℚ),
   (3538096872349317515413747668126903504889748654149258513456325721026423 /
    98177999178859923992739840000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine333_eq :
    IntervalRat.cosComputable input333 10 = cosine333 := by gerver_interval_eq

theorem sine333_eq :
    IntervalRat.sinComputable input333 10 = sine333 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 334. -/
def input334 : IntervalRat :=
  ⟨(11339 /
    320000 : ℚ),
   (91103 /
    2560000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input334` at Taylor depth ten. -/
def cosine334 : IntervalRat :=
  ⟨(0xaa97d2f5aa4a4d2c4a007602160ae1dd95b1dc0d1b5cd3cb39d8cffbafbc51161 /
    0xaab37e1bafdc580fe1e3807f63a72500000000000000000000000000000000000 : ℚ),
   (0x81f9f3880ef69e7b3c51e7b2cd9de638dd8161e870479aa41cdbb4d76eea6ce3 /
    0x820ed9fcb6c043184a94f4304bed100000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input334` at Taylor depth ten. -/
def sine334 : IntervalRat :=
  ⟨(0xac03e86f65f51c493d73e706de19306fe2d4c3a45f24f8e0f4d127a9287ac99 /
    0x12f77fca2ffc09c8e035b8f1b5bd3d00000000000000000000000000000000000 : ℚ),
   (0x2064564c3bd2455b5387f2941c0c7c65a82536b4e37e5dd9fff9c1f04868fa35 /
    0x38e67f5e8ff41d5aa0a12ad52137b700000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine334_eq :
    IntervalRat.cosComputable input334 10 = cosine334 := by gerver_interval_eq

theorem sine334_eq :
    IntervalRat.sinComputable input334 10 = sine334 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 335. -/
def input335 : IntervalRat :=
  ⟨(91103 /
    2560000 : ℚ),
   (45747 /
    1280000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input335` at Taylor depth ten. -/
def cosine335 : IntervalRat :=
  ⟨(7442227399378365176605227419825561222754297464362932355011449793271550437 /
    7446983048826115716190044160000000000000000000000000000000000000000000000 : ℚ),
   (7442267963384180440582224590651347758856234371569607523487407425354549563 /
    7446983048826115716190044160000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input335` at Taylor depth ten. -/
def sine335 : IntervalRat :=
  ⟨(264960184618418796258458741067268072581721975985585218880209107929070437 /
    7446983048826115716190044160000000000000000000000000000000000000000000000 : ℚ),
   (38013976577593633848747897805190556646072488222862064316424673724418509 /
    1063854721260873673741434880000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine335_eq :
    IntervalRat.cosComputable input335 10 = cosine335 := by gerver_interval_eq

theorem sine335_eq :
    IntervalRat.sinComputable input335 10 = sine335 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 336. -/
def input336 : IntervalRat :=
  ⟨(23069 /
    640000 : ℚ),
   (92667 /
    2560000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input336` at Taylor depth ten. -/
def cosine336 : IntervalRat :=
  ⟨(0x21b2580a23ea7eb58b87d130e5385a51bcea6d5b835beaf64c85595d49b0b0cd /
    0x21b7ffa0554e4a48ab0a2c585f89500000000000000000000000000000000000 : ℚ),
   (0x21b2643b280edecaf4ca4fc18e2e08821caf95670ec11d40b40e0170301f4f33 /
    0x21b7ffa0554e4a48ab0a2c585f89500000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input336` at Taylor depth ten. -/
def sine336 : IntervalRat :=
  ⟨(549622199633947875536783331183400149649206642325544521695323617246834634957 /
    0x21b7ffa0554e4a48ab0a2c585f89500000000000000000000000000000000000 : ℚ),
   (551952122523384932905905938408528397072516704327751362428441069601165365043 /
    0x21b7ffa0554e4a48ab0a2c585f89500000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine336_eq :
    IntervalRat.cosComputable input336 10 = cosine336 := by gerver_interval_eq

theorem sine336_eq :
    IntervalRat.sinComputable input336 10 = sine336 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 337. -/
def input337 : IntervalRat :=
  ⟨(92667 /
    2560000 : ℚ),
   (46529 /
    1280000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input337` at Taylor depth ten. -/
def cosine337 : IntervalRat :=
  ⟨(86115305536500246263178688499741057409563031513897453391592864549627378953 /
    86172232422130767573056225280000000000000000000000000000000000000000000000 : ℚ),
   (86115782960827023664867715766276086714968497835354624579502427553817241047 /
    86172232422130767573056225280000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input337` at Taylor depth ten. -/
def sine337 : IntervalRat :=
  ⟨(3118579597846168812040129634824708965347456145794478499038591808866818953 /
    86172232422130767573056225280000000000000000000000000000000000000000000000 : ℚ),
   (3131743946465900558360520069234828865545519790541190492976985791133181047 /
    86172232422130767573056225280000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine337_eq :
    IntervalRat.cosComputable input337 10 = cosine337 := by gerver_interval_eq

theorem sine337_eq :
    IntervalRat.sinComputable input337 10 = sine337 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 338. -/
def input338 : IntervalRat :=
  ⟨(46529 /
    1280000 : ℚ),
   (93449 /
    2560000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input338` at Taylor depth ten. -/
def cosine338 : IntervalRat :=
  ⟨(0xaa96618194ba6311fca9c22b68edaebb4274fce63fffc67ca2d671f681e41e8e7 /
    0xaab37e1bafdc580fe1e3807f63a72500000000000000000000000000000000000 : ℚ),
   (0x38dcdfea7280a4a6de70fd8af5762ef807c76cabe8625006bb8ed1d36358d07b3 /
    0x38e67f5e8ff41d5aa0a12ad52137b700000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input338` at Taylor depth ten. -/
def sine338 : IntervalRat :=
  ⟨(0xb076452b39ea56645f53ec0a059da63c2b966ccf2721e091f00b9dce444fd6f /
    0x12f77fca2ffc09c8e035b8f1b5bd3d00000000000000000000000000000000000 : ℚ),
   (0x3b11632c995b17667ed8c4ff747090ef3f2af74edeb7f334b8cfde893e900db /
    0x6527fee0ffeadeda011e85091e9bf00000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine338_eq :
    IntervalRat.cosComputable input338 10 = cosine338 := by gerver_interval_eq

theorem sine338_eq :
    IntervalRat.sinComputable input338 10 = sine338 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 339. -/
def input339 : IntervalRat :=
  ⟨(93449 /
    2560000 : ℚ),
   (1173 /
    32000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input339` at Taylor depth ten. -/
def cosine339 : IntervalRat :=
  ⟨(22711121889653607007256554101641578663867836439888815175181 /
    22726388698810167590912000000000000000000000000000000000000 : ℚ),
   (20764570388218312111161802125654113332589002490067830595971347 /
    20778412524626438940262400000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input339` at Taylor depth ten. -/
def sine339 : IntervalRat :=
  ⟨(5183795704040791825621202297949255596725338957577651139 /
    142039929367563547443200000000000000000000000000000000000 : ℚ),
   (650686865293083350447272855076399070453823732904923667 /
    17754991170945443430400000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine339_eq :
    IntervalRat.cosComputable input339 10 = cosine339 := by gerver_interval_eq

theorem sine339_eq :
    IntervalRat.sinComputable input339 10 = sine339 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 340. -/
def input340 : IntervalRat :=
  ⟨(92667 /
    2560000 : ℚ),
   (7429 /
    204800 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input340` at Taylor depth ten. -/
def cosine340 : IntervalRat :=
  ⟨(16569882434219989682680355301330916893660321375412386643012258211910203 /
    16580790019421040598602089269937018241024000000000000000000000000000000 : ℚ),
   (10356205198475453476404959796465958129154235756144492023940459278302723573 /
    10362993762138150374126305793710636400640000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input340` at Taylor depth ten. -/
def sine340 : IntervalRat :=
  ⟨(120012119501094576982284998441082948865244271956745700135238551723327 /
    3316158003884208119720417853987403648204800000000000000000000000000000 : ℚ),
   (4810616823441761479322454010199163115798919901578197497302511381737 /
    132646320155368324788816714159496145928192000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine340_eq :
    IntervalRat.cosComputable input340 10 = cosine340 := by gerver_interval_eq

theorem sine340_eq :
    IntervalRat.sinComputable input340 10 = sine340 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 341. -/
def input341 : IntervalRat :=
  ⟨(7429 /
    204800 : ℚ),
   (46529 /
    1280000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input341` at Taylor depth ten. -/
def cosine341 : IntervalRat :=
  ⟨(9568367284750799587338255629453160437499550421948903222746483176830688217 /
    9574692491347863063672913920000000000000000000000000000000000000000000000 : ℚ),
   (172231089052393102606174684177624926475728563675233795404415064268951908969 /
    172344464844261535146112450560000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input341` at Taylor depth ten. -/
def sine341 : IntervalRat :=
  ⟨(1041719626629552813794062016687869604225756883782794008406917872288939651 /
    28724077474043589191018741760000000000000000000000000000000000000000000000 : ℚ),
   (1043913685747872624380895635646436057522269800189543290286832127711060349 /
    28724077474043589191018741760000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine341_eq :
    IntervalRat.cosComputable input341 10 = cosine341 := by gerver_interval_eq

theorem sine341_eq :
    IntervalRat.sinComputable input341 10 = sine341 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 342. -/
def input342 : IntervalRat :=
  ⟨(46529 /
    1280000 : ℚ),
   (186507 /
    5120000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input342` at Taylor depth ten. -/
def cosine342 : IntervalRat :=
  ⟨(0x10d922d489665dae97c8e396ad4c2209049f5b0aad9bcc8ae8ac5b96d33395bac1d /
    0x10dbffd02aa725245585162c2fc4a80000000000000000000000000000000000000 : ℚ),
   (0x10d925e69076d746202e52d409200b819b5ea634753dc6c0ce28d1121fb8c4453e3 /
    0x10dbffd02aa725245585162c2fc4a80000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input342` at Taylor depth ten. -/
def sine342 : IntervalRat :=
  ⟨(0x9cdaf1b19580702b368d88c110242e7bdb254894f837119411df901d87dbbac1d /
    0x10dbffd02aa725245585162c2fc4a80000000000000000000000000000000000000 : ℚ),
   (0x9d2f572c9cbdaa7648e121b81882bce2acddf8db62d1cc6274f6f19ef824453e3 /
    0x10dbffd02aa725245585162c2fc4a80000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine342_eq :
    IntervalRat.cosComputable input342 10 = cosine342 := by gerver_interval_eq

theorem sine342_eq :
    IntervalRat.sinComputable input342 10 = sine342 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 343. -/
def input343 : IntervalRat :=
  ⟨(186507 /
    5120000 : ℚ),
   (93449 /
    2560000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input343` at Taylor depth ten. -/
def cosine343 : IntervalRat :=
  ⟨(0xaa96618276f4203c4690fb20fef65320bf1722795b1dbe8541ca105e409d4ade7 /
    0xaab37e1bafdc580fe1e3807f63a72500000000000000000000000000000000000 : ℚ),
   (0xaa9680a9b234dc0682a28783bb95163d06a421863e2c1c45b3c98c96c3f0a5a59 /
    0xaab37e1bafdc580fe1e3807f63a72500000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input343` at Taylor depth ten. -/
def sine343 : IntervalRat :=
  ⟨(0x6377e912dafba3bf625680179e73a32b2eba37a236ba4b58c5b54023033ce8e7 /
    0xaab37e1bafdc580fe1e3807f63a72500000000000000000000000000000000000 : ℚ),
   (0x63ad514df45ab34ac6a439b741d144a686652200c79fe491c1825dcd21731719 /
    0xaab37e1bafdc580fe1e3807f63a72500000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine343_eq :
    IntervalRat.cosComputable input343 10 = cosine343 := by gerver_interval_eq

theorem sine343_eq :
    IntervalRat.sinComputable input343 10 = sine343 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 344. -/
def input344 : IntervalRat :=
  ⟨(93449 /
    2560000 : ℚ),
   (187289 /
    5120000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input344` at Taylor depth ten. -/
def cosine344 : IntervalRat :=
  ⟨(0x97a2020aefddd5e9c53053512d276c7aff2dcee9541a6efb12300ff8d1d21e4e8bf /
    0x97bbfe517fe04e4701adc78dade9e80000000000000000000000000000000000000 : ℚ),
   (0x554b30c21e6a1c95f9689699b4980dda5c084c970390e1d9230e5a1973610c45d149 /
    0x5559bf0dd7ee2c07f0f1c03fb1d39280000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input344` at Taylor depth ten. -/
def sine344 : IntervalRat :=
  ⟨(0x109ce0dc43bb40c8172cd1367c32841e1b315036ff7de5f14a297abb8eaf720ba3d /
    0x1c733faf47fa0ead5050956a909bdb80000000000000000000000000000000000000 : ℚ),
   (0x9dd7fbe69e7ca978f50fa748ec297132e64d6ee2c9fc244a1803aec71f21b3b79 /
    0x10dbffd02aa725245585162c2fc4a80000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine344_eq :
    IntervalRat.cosComputable input344 10 = cosine344 := by gerver_interval_eq

theorem sine344_eq :
    IntervalRat.sinComputable input344 10 = sine344 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 345. -/
def input345 : IntervalRat :=
  ⟨(187289 /
    5120000 : ℚ),
   (1173 /
    32000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input345` at Taylor depth ten. -/
def cosine345 : IntervalRat :=
  ⟨(51911135764010598429300242546152688263217814078290058657803 /
    51946031311566097350656000000000000000000000000000000000000 : ℚ),
   (9302501560014551165663960553464410311721910818785691571503751269 /
    9308728811032644645237555200000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input345` at Taylor depth ten. -/
def sine345 : IntervalRat :=
  ⟨(166228494888083332976277242766132695082050110462220957723 /
    4545277739762033518182400000000000000000000000000000000000 : ℚ),
   (5205490079466038784129143177185362719193038286282036211 /
    142039929367563547443200000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine345_eq :
    IntervalRat.cosComputable input345 10 = cosine345 := by gerver_interval_eq

theorem sine345_eq :
    IntervalRat.sinComputable input345 10 = sine345 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 346. -/
def input346 : IntervalRat :=
  ⟨(1173 /
    32000 : ℚ),
   (94231 /
    2560000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input346` at Taylor depth ten. -/
def cosine346 : IntervalRat :=
  ⟨(0xaa95e444c565af07a7b4ac488eed6f0c20d4bef87cd76ccd548b4ad57c4967cb9 /
    0xaab37e1bafdc580fe1e3807f63a72500000000000000000000000000000000000 : ℚ),
   (0xaa96230825fca03743dc686c41132c03c4721c7c67355b0e35c999f038b698347 /
    0xaab37e1bafdc580fe1e3807f63a72500000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input346` at Taylor depth ten. -/
def sine346 : IntervalRat :=
  ⟨(0x6417f7159e71a2a4dc9ab05915e126ecbdbee0eccb7e6aae6fb4ac4c74967cb9 /
    0xaab37e1bafdc580fe1e3807f63a72500000000000000000000000000000000000 : ℚ),
   (0xe5bd360606847d222486e7e89c602c60b947c1033ecba0ef48d9e875d0f12c1 /
    0x1862c8df62440c948dfbedc90e3c7300000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine346_eq :
    IntervalRat.cosComputable input346 10 = cosine346 := by gerver_interval_eq

theorem sine346_eq :
    IntervalRat.sinComputable input346 10 = sine346 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 347. -/
def input347 : IntervalRat :=
  ⟨(94231 /
    2560000 : ℚ),
   (47311 /
    1280000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input347` at Taylor depth ten. -/
def cosine347 : IntervalRat :=
  ⟨(54799421196928313857878829333679182277006179375462145520138768649806518099 /
    54836875177719579364672143360000000000000000000000000000000000000000000000 : ℚ),
   (2609510958538161865264451801548388426534001228872619517614800980695456281 /
    2611279770367599017365340160000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input347` at Taylor depth ten. -/
def sine347 : IntervalRat :=
  ⟨(224225568130023515598328285379802079807681745825053073075859405915222011 /
    6092986130857731040519127040000000000000000000000000000000000000000000000 : ℚ),
   (675469162776115201510870776284164520739744748111800864697368214254333967 /
    18278958392573193121557381120000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine347_eq :
    IntervalRat.cosComputable input347 10 = cosine347 := by gerver_interval_eq

theorem sine347_eq :
    IntervalRat.sinComputable input347 10 = sine347 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 348. -/
def input348 : IntervalRat :=
  ⟨(47311 /
    1280000 : ℚ),
   (95013 /
    2560000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input348` at Taylor depth ten. -/
def cosine348 : IntervalRat :=
  ⟨(0x21b20dd32476a6b617ecb1c8d2f58b243686f96fb77b4cad023e02b3f255b3d3 /
    0x21b7ffa0554e4a48ab0a2c585f89500000000000000000000000000000000000 : ℚ),
   (0x21b21a5356b71d803a6b66c7eae7e85c1e26a7d2fa02133e397b131bf5fb4c2d /
    0x21b7ffa0554e4a48ab0a2c585f89500000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input348` at Taylor depth ten. -/
def sine348 : IntervalRat :=
  ⟨(563589334080500152694628551266111497589020741682750314489517462883061511123 /
    0x21b7ffa0554e4a48ab0a2c585f89500000000000000000000000000000000000 : ℚ),
   (565919283002344321656468887638226283597004912319427813720449067676938488877 /
    0x21b7ffa0554e4a48ab0a2c585f89500000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine348_eq :
    IntervalRat.cosComputable input348 10 = cosine348 := by gerver_interval_eq

theorem sine348_eq :
    IntervalRat.sinComputable input348 10 = sine348 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 349. -/
def input349 : IntervalRat :=
  ⟨(95013 /
    2560000 : ℚ),
   (23851 /
    640000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input349` at Taylor depth ten. -/
def cosine349 : IntervalRat :=
  ⟨(294329490234353454480357045874591955887833475300674159306498674516947649 /
    294533997536579771978219520000000000000000000000000000000000000000000000 : ℚ),
   (1177324653122984564816978522871544024967604541905602355782121438749187529 /
    1178135990146319087912878080000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input349` at Taylor depth ten. -/
def sine349 : IntervalRat :=
  ⟨(10928938070220130580915849049563764432549190118274149893314269283875149 /
    294533997536579771978219520000000000000000000000000000000000000000000000 : ℚ),
   (10973933907251519071426070089365698258449571234539254740694158716124851 /
    294533997536579771978219520000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine349_eq :
    IntervalRat.cosComputable input349 10 = cosine349 := by gerver_interval_eq

theorem sine349_eq :
    IntervalRat.sinComputable input349 10 = sine349 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 350. -/
def input350 : IntervalRat :=
  ⟨(23851 /
    640000 : ℚ),
   (19159 /
    512000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input350` at Taylor depth ten. -/
def cosine350 : IntervalRat :=
  ⟨(18058976018314504295311316517871533801589437343842388258593230565089147 /
    18071626956853638347737000895840256000000000000000000000000000000000000 : ℚ),
   (16721369530046756573279479165096258237592908714027854591849793299351751 /
    16732987923012628099756482310963200000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input350` at Taylor depth ten. -/
def sine350 : IntervalRat :=
  ⟨(14962701066424707629200090154616967878785555506625218987372762120007 /
    401591710152303074394155575463116800000000000000000000000000000000000 : ℚ),
   (45072156547027927923105776051639092835941879136735523319680251675179 /
    1204775130456909223182466726389350400000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine350_eq :
    IntervalRat.cosComputable input350 10 = cosine350 := by gerver_interval_eq

theorem sine350_eq :
    IntervalRat.sinComputable input350 10 = sine350 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 351. -/
def input351 : IntervalRat :=
  ⟨(19159 /
    512000 : ℚ),
   (48093 /
    1280000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input351` at Taylor depth ten. -/
def cosine351 : IntervalRat :=
  ⟨(7441727192429717864921096106676956767238609636199155649575991784378122603 /
    7446983048826115716190044160000000000000000000000000000000000000000000000 : ℚ),
   (7441769841095403432210348545668015093978925576259650356153424354234377397 /
    7446983048826115716190044160000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input351` at Taylor depth ten. -/
def sine351 : IntervalRat :=
  ⟨(278599962919541309946833135180053694340819416763219127155709717328122603 /
    7446983048826115716190044160000000000000000000000000000000000000000000000 : ℚ),
   (279737639766552121807837712313882220013939385776418466019010282671877397 /
    7446983048826115716190044160000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine351_eq :
    IntervalRat.cosComputable input351 10 = cosine351 := by gerver_interval_eq

theorem sine351_eq :
    IntervalRat.sinComputable input351 10 = sine351 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 352. -/
def input352 : IntervalRat :=
  ⟨(48093 /
    1280000 : ℚ),
   (192763 /
    5120000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input352` at Taylor depth ten. -/
def cosine352 : IntervalRat :=
  ⟨(0x554a433ec429b085226fa5ab36f636713c1e9ebb248dbb844262d96667ac81ad8bdd /
    0x5559bf0dd7ee2c07f0f1c03fb1d39280000000000000000000000000000000000000 : ℚ),
   (0x554a534fa5bc8103cb8dd37c1abeccff59aa7ef64425889d28dba304ffc133f27423 /
    0x5559bf0dd7ee2c07f0f1c03fb1d39280000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input352` at Taylor depth ten. -/
def sine352 : IntervalRat :=
  ⟨(0x334c252e8b3b192009fef83298dced0982abdc4108f8c6876afac9bf097660d8bdd /
    0x5559bf0dd7ee2c07f0f1c03fb1d39280000000000000000000000000000000000000 : ℚ),
   (0x3366d964d75fd0e6a3a6eb4f46d819021d08bc15d0106e068cf56bc4f3099f27423 /
    0x5559bf0dd7ee2c07f0f1c03fb1d39280000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine352_eq :
    IntervalRat.cosComputable input352 10 = cosine352 := by gerver_interval_eq

theorem sine352_eq :
    IntervalRat.sinComputable input352 10 = sine352 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 353. -/
def input353 : IntervalRat :=
  ⟨(192763 /
    5120000 : ℚ),
   (96577 /
    2560000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input353` at Taylor depth ten. -/
def cosine353 : IntervalRat :=
  ⟨(0x2b52631fbfd9a662eaaa0fc5b00a225a8f85257d923204aef2defaef48999101 /
    0x2b5a48a99240165d6e31a6bac3f9b00000000000000000000000000000000000 : ℚ),
   (0xaa94867f7a488dc64150388901661d335065c7f0840e7592f91f64f5ff960b901 /
    0xaab37e1bafdc580fe1e3807f63a72500000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input353` at Taylor depth ten. -/
def sine353 : IntervalRat :=
  ⟨(0x22448c9fba44b6800f29093a0eee4d3a4e8c35f515b2b488ee87723f22509e15 /
    0x38e67f5e8ff41d5aa0a12ad52137b700000000000000000000000000000000000 : ℚ),
   (0x22565a1a6095f58114cf7f6711bb9f4b987af7fc1ecb3fee44852b3acf3f61eb /
    0x38e67f5e8ff41d5aa0a12ad52137b700000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine353_eq :
    IntervalRat.cosComputable input353 10 = cosine353 := by gerver_interval_eq

theorem sine353_eq :
    IntervalRat.sinComputable input353 10 = sine353 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 354. -/
def input354 : IntervalRat :=
  ⟨(96577 /
    2560000 : ℚ),
   (38709 /
    1024000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input354` at Taylor depth ten. -/
def cosine354 : IntervalRat :=
  ⟨(290560898474968511276127851319471651840700273652818026371716890791780333 /
    290768624077950347197707794436325376000000000000000000000000000000000000 : ℚ),
   (7264043425550325829278721753090257760573703509526279038288178971664376283 /
    7269215601948758679942694860908134400000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input354` at Taylor depth ten. -/
def sine354 : IntervalRat :=
  ⟨(2193349524880198762377491447984061286783827965977481043365995586022601 /
    58153724815590069439541558887265075200000000000000000000000000000000000 : ℚ),
   (2197791616912315413609368080700608712299437687296620156187082435302199 /
    58153724815590069439541558887265075200000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine354_eq :
    IntervalRat.cosComputable input354 10 = cosine354 := by gerver_interval_eq

theorem sine354_eq :
    IntervalRat.sinComputable input354 10 = sine354 := by gerver_interval_eq

/-- The common first-angle interval in cache entry 355. -/
def input355 : IntervalRat :=
  ⟨(38709 /
    1024000 : ℚ),
   (12121 /
    320000 : ℚ),
   by decide +kernel⟩

/-- Exact cosine enclosure for `input355` at Taylor depth ten. -/
def cosine355 : IntervalRat :=
  ⟨(18395170688946122188116906296828270630088156040920450132504586053102037 /
    18408374846036235748638720000000000000000000000000000000000000000000000 : ℚ),
   (4709177314349474500106749820573435628129155937736902664458205534089081653 /
    4712543960585276351651512320000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

/-- Exact sine enclosure for `input355` at Taylor depth ten. -/
def sine355 : IntervalRat :=
  ⟨(10870352181405328748837190997328221700948661208843885267545952068733 /
    287630856969316183572480000000000000000000000000000000000000000000000 : ℚ),
   (5446161491649438115889129793927701772864541164346792089939792520321 /
    143815428484658091786240000000000000000000000000000000000000000000000 : ℚ),
   by decide +kernel⟩

theorem cosine355_eq :
    IntervalRat.cosComputable input355 10 = cosine355 := by gerver_interval_eq

theorem sine355_eq :
    IntervalRat.sinComputable input355 10 = sine355 := by gerver_interval_eq

end GerverSofa.PartE.CachedIntervals

open Lean Meta Elab Tactic in
/-- Reuse exact first-angle evaluations while preserving the leaf's auxiliary declaration. -/
elab (name := gerverCachedRejected) "gerver_cached_rejected " index:num : tactic =>
  closeMainGoalUsing `gerver_cached_rejected fun expectedType _ => do
    let expectedType ← instantiateMVars expectedType
    unless expectedType.isAppOfArity ``Eq 3 do throwError "expected a rejection equality"
    let expression := expectedType.appFn!.appArg!
    unless expression.isAppOfArity ``GerverSofa.PartE.AngleCell.rejected 2 do
      throwError "expected an AngleCell rejection test"
    let arguments := expression.getAppArgs
    let prefixName := `GerverSofa.PartE.CachedIntervals
    let number := index.getNat
    let cosine := mkConst (prefixName ++ Name.mkSimple s!"cosine{number}")
    let sine := mkConst (prefixName ++ Name.mkSimple s!"sine{number}")
    let cosineEquality := mkConst (prefixName ++ Name.mkSimple s!"cosine{number}_eq")
    let sineEquality := mkConst (prefixName ++ Name.mkSimple s!"sine{number}_eq")
    let reflexivity := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
    let proof := mkAppN (mkConst ``GerverSofa.PartE.CachedIntervals.rejected_of_cached)
      #[arguments[0]!, arguments[1]!, cosine, sine, cosineEquality, sineEquality, reflexivity]
    let name ← mkAuxLemma [] expectedType proof
    pure (mkConst name)
