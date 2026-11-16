/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle005

import LeanPool.MovingSofa.KernelCertificate
public meta import LeanPool.MovingSofa.KernelCertificate

/-! # Exact trigonometric values shared by frequently used certificate intervals

Each equality is independently checked by the kernel against the original Taylor evaluator.
-/

@[expose] public section

namespace GerverSofa.PartE.CertificateCache

open LeanCert.Core GerverSofa.PartALeanCert

/-- Exact rational interval input000. -/
def input000 : IntervalRat :=
  ⟨(q
    53
    1280),
    (q
    27
    640), by certificate_kernel⟩

/-- Exact rational interval sin000. -/
def sin000 : IntervalRat :=
  ⟨(q
    150517667526113521659780002416619117
    3636222191809626814545920000000000000),
    (q
    153359293249258178603743691926676883
    3636222191809626814545920000000000000), by certificate_kernel⟩

/-- Exact rational interval cos000. -/
def cos000 : IntervalRat :=
  ⟨(q
    3632986806956899008956153304193235957
    3636222191809626814545920000000000000),
    (q
    3633105543461361130958447286397514293
    3636222191809626814545920000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin000_eq : IntervalRat.sinComputable input000 10 = sin000 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos000_eq : IntervalRat.cosComputable input000 10 = cos000 := by
  certificate_kernel

/-- Exact rational interval input001. -/
def input001 : IntervalRat :=
  ⟨(q
    103
    2560),
    (q
    13
    320), by certificate_kernel⟩

/-- Exact rational interval sin001. -/
def sin001 : IntervalRat :=
  ⟨(q
    7712976524636283329811259964585159
    191753904646210789048320000000000000),
    (q
    1946975200159236605953184868869929
    47938476161552697262080000000000000), by certificate_kernel⟩

/-- Exact rational interval cos001. -/
def cos001 : IntervalRat :=
  ⟨(q
    9196593195247565974558889421965581537
    9204187423018117874319360000000000000),
    (q
    196197089185481121433662860509518344419
    196355998357719847985479680000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin001_eq : IntervalRat.sinComputable input001 10 = sin001 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos001_eq : IntervalRat.cosComputable input001 10 = cos001 := by
  certificate_kernel

/-- Exact rational interval input002. -/
def input002 : IntervalRat :=
  ⟨(q
    13
    320),
    (q
    53
    1280), by certificate_kernel⟩

/-- Exact rational interval sin002. -/
def sin002 : IntervalRat :=
  ⟨(q
    8166075631836176005951491998256747338801
    201068542318305124337131192320000000000000),
    (q
    8323204473706604773460553393876741301199
    201068542318305124337131192320000000000000), by certificate_kernel⟩

/-- Exact rational interval cos002. -/
def cos002 : IntervalRat :=
  ⟨(q
    7440600084176608048479779737463608807843
    7446983048826115716190044160000000000000),
    (q
    602707935612045512018677416623657812224877
    603205626954915373011393576960000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin002_eq : IntervalRat.sinComputable input002 10 = sin002 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos002_eq : IntervalRat.cosComputable input002 10 = cos002 := by
  certificate_kernel

/-- Exact rational interval input003. -/
def input003 : IntervalRat :=
  ⟨(q
    203
    5120),
    (q
    51
    1280), by certificate_kernel⟩

/-- Exact rational interval sin003. -/
def sin003 : IntervalRat :=
  ⟨(q
    295183125710098218198847903082791734629
    7446983048826115716190044160000000000000),
    (q
    296637997570037377479315346803916697371
    7446983048826115716190044160000000000000), by certificate_kernel⟩

/-- Exact rational interval cos003. -/
def cos003 : IntervalRat :=
  ⟨(q
    3720536344721201270972986226411841454787
    3723491524413057858095022080000000000000),
    (q
    119058087995104894265511986852395218401441
    119151728781217851459040706560000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin003_eq : IntervalRat.sinComputable input003 10 = sin003 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos003_eq : IntervalRat.cosComputable input003 10 = cos003 := by
  certificate_kernel

/-- Exact rational interval input004. -/
def input004 : IntervalRat :=
  ⟨(q
    161
    4096),
    (q
    403
    10240), by certificate_kernel⟩

/-- Exact rational interval sin004. -/
def sin004 : IntervalRat :=
  ⟨(q
    67871554922072254059602319849616647829954656535751
    1727165627023025062354384298951772733440000000000000),
    (q
    67955910926103114828010636129529310943334303464249
    1727165627023025062354384298951772733440000000000000), by certificate_kernel⟩

/-- Exact rational interval cos004. -/
def cos004 : IntervalRat :=
  ⟨(q
    1725828236463848468380876730386799850832914419335751
    1727165627023025062354384298951772733440000000000000),
    (q
    5177494660257685400194935893032379207280266602892747
    5181496881069075187063152896855318200320000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin004_eq : IntervalRat.sinComputable input004 10 = sin004 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos004_eq : IntervalRat.cosComputable input004 10 = cos004 := by
  certificate_kernel

/-- Exact rational interval input005. -/
def input005 : IntervalRat :=
  ⟨(q
    51
    1280),
    (q
    103
    2560), by certificate_kernel⟩

/-- Exact rational interval sin005. -/
def sin005 : IntervalRat :=
  ⟨(q
    49208300191084035845211228743188807018650953
    1235365124003666683927334045614080000000000000),
    (q
    49690993635240274421952830266775403894629047
    1235365124003666683927334045614080000000000000), by certificate_kernel⟩

/-- Exact rational interval cos005. -/
def cos005 : IntervalRat :=
  ⟨(q
    1234365348700446237058309938288792763925904713
    1235365124003666683927334045614080000000000000),
    (q
    1234384670130822564457483086761446273080615607
    1235365124003666683927334045614080000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin005_eq : IntervalRat.sinComputable input005 10 = sin005 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos005_eq : IntervalRat.cosComputable input005 10 = cos005 := by
  certificate_kernel

/-- Exact rational interval input006. -/
def input006 : IntervalRat :=
  ⟨(q
    403
    10240),
    (q
    101
    2560), by certificate_kernel⟩

/-- Exact rational interval sin006. -/
def sin006 : IntervalRat :=
  ⟨(q
    16201920565087825434422353422693146021573633
    411788374667888894642444681871360000000000000),
    (q
    16242144680971672792685093196530780869882367
    411788374667888894642444681871360000000000000), by certificate_kernel⟩

/-- Exact rational interval cos006. -/
def cos006 : IntervalRat :=
  ⟨(q
    1234403794874191709841687972751785342426081989
    1235365124003666683927334045614080000000000000),
    (q
    3291756129741183428204469314640938454094291571
    3294306997343111157139557454970880000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin006_eq : IntervalRat.sinComputable input006 10 = sin006 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos006_eq : IntervalRat.cosComputable input006 10 = cos006 := by
  certificate_kernel

/-- Exact rational interval input007. -/
def input007 : IntervalRat :=
  ⟨(q
    1607
    40960),
    (q
    201
    5120), by certificate_kernel⟩

/-- Exact rational interval sin007. -/
def sin007 : IntervalRat :=
  ⟨(q
    1225136951634664621074188601578125618654775479
    31234910789623572452878766980464640000000000000),
    (q
    1225899718468143754666955926811978034386544521
    31234910789623572452878766980464640000000000000), by certificate_kernel⟩

/-- Exact rational interval cos007. -/
def cos007 : IntervalRat :=
  ⟨(q
    124843378527575162591592181377466606841654836261
    124939643158494289811515067921858560000000000000),
    (q
    7989983887221021524391667007713856875814545098281
    7996137162143634547936964346998947840000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin007_eq : IntervalRat.sinComputable input007 10 = sin007 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos007_eq : IntervalRat.cosComputable input007 10 = cos007 := by
  certificate_kernel

/-- Exact rational interval input008. -/
def input008 : IntervalRat :=
  ⟨(q
    3213
    81920),
    (q
    1607
    40960), by certificate_kernel⟩

/-- Exact rational interval sin008. -/
def sin008 : IntervalRat :=
  ⟨(q
    852166596446426185491636631292982742093743952231054514857
    21732773094255546333399730447891848548874977280000000000000),
    (q
    852431957129834563668885869771631908736082989872399181143
    21732773094255546333399730447891848548874977280000000000000), by certificate_kernel⟩

/-- Exact rational interval cos008. -/
def cos008 : IntervalRat :=
  ⟨(q
    21716049049007429658300489649222574853588408153933085928617
    21732773094255546333399730447891848548874977280000000000000),
    (q
    21716059455720140179057957429117802244595485326083747853783
    21732773094255546333399730447891848548874977280000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin008_eq : IntervalRat.sinComputable input008 10 = sin008 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos008_eq : IntervalRat.cosComputable input008 10 = cos008 := by
  certificate_kernel

/-- Exact rational interval input009. -/
def input009 : IntervalRat :=
  ⟨(q
    101
    2560),
    (q
    81
    2048), by certificate_kernel⟩

/-- Exact rational interval sin009. -/
def sin009 : IntervalRat :=
  ⟨(q
    32295972688773708440744521435784112185689967
    818804445403508177708745149132692258816000000),
    (q
    6475190971466115620152998512114291843553309
    163760889080701635541749029826538451763200000), by certificate_kernel⟩

/-- Exact rational interval cos009. -/
def cos009 : IntervalRat :=
  ⟨(q
    818164115188451480149113205225174794793797487
    818804445403508177708745149132692258816000000),
    (q
    20454181845470661104447328616379459088994469417
    20470111135087704442718628728317306470400000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin009_eq : IntervalRat.sinComputable input009 10 = sin009 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos009_eq : IntervalRat.cosComputable input009 10 = cos009 := by
  certificate_kernel

/-- Exact rational interval input010. -/
def input010 : IntervalRat :=
  ⟨(q
    81
    2048),
    (q
    203
    5120), by certificate_kernel⟩

/-- Exact rational interval sin010. -/
def sin010 : IntervalRat :=
  ⟨(q
    14291194314211175663335605724654817064692473579
    361432539137072766954740017916805120000000000000),
    (q
    14326499686139393402508140281011048576267526421
    361432539137072766954740017916805120000000000000), by certificate_kernel⟩

/-- Exact rational interval cos010. -/
def cos010 : IntervalRat :=
  ⟨(q
    361148490445157692490995422188766073423341073579
    361432539137072766954740017916805120000000000000),
    (q
    361149888158777126695139411648919957845491276421
    361432539137072766954740017916805120000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin010_eq : IntervalRat.sinComputable input010 10 = sin010 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos010_eq : IntervalRat.cosComputable input010 10 = cos010 := by
  certificate_kernel

/-- Exact rational interval input011. -/
def input011 : IntervalRat :=
  ⟨(q
    803
    20480),
    (q
    3213
    81920), by certificate_kernel⟩

/-- Exact rational interval sin011. -/
def sin011 : IntervalRat :=
  ⟨(q
    3077062236471397528326669887061704769417797965425704866189
    78498623098827793458205728319722232501051064320000000000000),
    (q
    3078020717234885901212506004638913470809852877073776733811
    78498623098827793458205728319722232501051064320000000000000), by certificate_kernel⟩

/-- Exact rational interval cos011. -/
def cos011 : IntervalRat :=
  ⟨(q
    78438253544711968811396541635137733045160969585927012913549
    78498623098827793458205728319722232501051064320000000000000),
    (q
    78438291121987656502337062741991059841451516987862500077171
    78498623098827793458205728319722232501051064320000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin011_eq : IntervalRat.sinComputable input011 10 = sin011 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos011_eq : IntervalRat.cosComputable input011 10 = cos011 := by
  certificate_kernel

/-- Exact rational interval input012. -/
def input012 : IntervalRat :=
  ⟨(q
    101
    2560),
    (q
    203
    5120), by certificate_kernel⟩

/-- Exact rational interval sin012. -/
def sin012 : IntervalRat :=
  ⟨(q
    1583989712580972714783900869507234648341019731
    40159171015230307439415557546311680000000000000),
    (q
    1591835345724829241716046962001838448526820269
    40159171015230307439415557546311680000000000000), by certificate_kernel⟩

/-- Exact rational interval cos012. -/
def cos012 : IntervalRat :=
  ⟨(q
    120382830087506161818228819130772512495313368313
    120477513045690922318246672638935040000000000000),
    (q
    361151282242867939372142329277475652660651106581
    361432539137072766954740017916805120000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin012_eq : IntervalRat.sinComputable input012 10 = sin012 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos012_eq : IntervalRat.cosComputable input012 10 = cos012 := by
  certificate_kernel

/-- Exact rational interval input013. -/
def input013 : IntervalRat :=
  ⟨(q
    27
    640),
    (q
    11
    256), by certificate_kernel⟩

/-- Exact rational interval sin013. -/
def sin013 : IntervalRat :=
  ⟨(q
    29602801261267208973686975536250423
    701912002274810615867803435008000000),
    (q
    6030267140687004072499860733909493
    140382400454962123173560687001600000), by certificate_kernel⟩

/-- Exact rational interval cos013. -/
def cos013 : IntervalRat :=
  ⟨(q
    701264123578975768914345776902680119
    701912002274810615867803435008000000),
    (q
    17532186802311203876237254891867778209
    17547800056870265396695085875200000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin013_eq : IntervalRat.sinComputable input013 10 = sin013 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos013_eq : IntervalRat.cosComputable input013 10 = cos013 := by
  certificate_kernel

/-- Exact rational interval input014. -/
def input014 : IntervalRat :=
  ⟨(q
    11
    256),
    (q
    7
    160), by certificate_kernel⟩

/-- Exact rational interval sin014. -/
def sin014 : IntervalRat :=
  ⟨(q
    2298213551984782949851791251797
    53502763573161492480000000000000),
    (q
    10833452238294522380076661233
    247697979505377280000000000000), by certificate_kernel⟩

/-- Exact rational interval cos014. -/
def cos014 : IntervalRat :=
  ⟨(q
    47512504563688345783676042321389
    47558012065032437760000000000000),
    (q
    82104391701747955049547933151849183
    82180244848376052449280000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin014_eq : IntervalRat.sinComputable input014 10 = sin014 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos014_eq : IntervalRat.cosComputable input014 10 = cos014 := by
  certificate_kernel

/-- Exact rational interval input015. -/
def input015 : IntervalRat :=
  ⟨(q
    201
    5120),
    (q
    161
    4096), by certificate_kernel⟩

/-- Exact rational interval sin015. -/
def sin015 : IntervalRat :=
  ⟨(q
    761572725286554854926565996982336008495067777049
    19404261691299594940535473614189150490066944000000),
    (q
    152504088538810307608862902907257118114859669499
    3880852338259918988107094722837830098013388800000), by certificate_kernel⟩

/-- Exact rational interval cos015. -/
def cos015 : IntervalRat :=
  ⟨(q
    19389273707819040422650104586544180138680014293017
    19404261691299594940535473614189150490066944000000),
    (q
    484732773167410919433702633143139463646826005132687
    485106542282489873513386840354728762251673600000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin015_eq : IntervalRat.sinComputable input015 10 = sin015 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos015_eq : IntervalRat.cosComputable input015 10 = cos015 := by
  certificate_kernel

/-- Exact rational interval input016. -/
def input016 : IntervalRat :=
  ⟨(q
    29
    640),
    (q
    3
    64), by certificate_kernel⟩

/-- Exact rational interval sin016. -/
def sin016 : IntervalRat :=
  ⟨(q
    1029412406454597649623782309
    22726388698810167590912000000),
    (q
    212986992160807219498978783
    4545277739762033518182400000), by certificate_kernel⟩

/-- Exact rational interval cos016. -/
def cos016 : IntervalRat :=
  ⟨(q
    22701425014227610479607998809
    22726388698810167590912000000),
    (q
    35473534066401084439043562709
    35509982341890886860800000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin016_eq : IntervalRat.sinComputable input016 10 = sin016 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos016_eq : IntervalRat.cosComputable input016 10 = cos016 := by
  certificate_kernel

/-- Exact rational interval input017. -/
def input017 : IntervalRat :=
  ⟨(q
    27
    640),
    (q
    7
    160), by certificate_kernel⟩

/-- Exact rational interval sin017. -/
def sin017 : IntervalRat :=
  ⟨(q
    423080221620846780162368852501
    10031768169967779840000000000000),
    (q
    438759681619404976342013926249
    10031768169967779840000000000000), by certificate_kernel⟩

/-- Exact rational interval cos017. -/
def cos017 : IntervalRat :=
  ⟨(q
    80177351025438259669380707469223
    80254145359742238720000000000000),
    (q
    1282923826915538610990901923066887
    1284066325755875819520000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin017_eq : IntervalRat.sinComputable input017 10 = sin017 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos017_eq : IntervalRat.cosComputable input017 10 = cos017 := by
  certificate_kernel

/-- Exact rational interval input018. -/
def input018 : IntervalRat :=
  ⟨(q
    7
    160),
    (q
    29
    640), by certificate_kernel⟩

/-- Exact rational interval sin018. -/
def sin018 : IntervalRat :=
  ⟨(q
    1431272580383130962992025775221638019
    32725999726286641330913280000000000000),
    (q
    4447271554841904783327132997582189943
    98177999178859923992739840000000000000), by certificate_kernel⟩

/-- Exact rational interval cos018. -/
def cos018 : IntervalRat :=
  ⟨(q
    294231673824789027338305122122314719131
    294533997536579771978219520000000000000),
    (q
    32694685280396868199192626481089084541
    32725999726286641330913280000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin018_eq : IntervalRat.sinComputable input018 10 = sin018 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos018_eq : IntervalRat.cosComputable input018 10 = cos018 := by
  certificate_kernel

/-- Exact rational interval input019. -/
def input019 : IntervalRat :=
  ⟨(q
    51
    1280),
    (q
    41
    1024), by certificate_kernel⟩

/-- Exact rational interval sin019. -/
def sin019 : IntervalRat :=
  ⟨(q
    1289969435939715235938186456924344435404183
    32384355506681719919144705605345738752000000),
    (q
    259259237449210273535955983901467251927573
    6476871101336343983828941121069147750400000), by certificate_kernel⟩

/-- Exact rational interval cos019. -/
def cos019 : IntervalRat :=
  ⟨(q
    32358400830924491902713825354763765421763991
    32384355506681719919144705605345738752000000),
    (q
    808966336577353415584532193207653948963736641
    809608887667042997978617640133643468800000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin019_eq : IntervalRat.sinComputable input019 10 = sin019 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos019_eq : IntervalRat.cosComputable input019 10 = cos019 := by
  certificate_kernel

/-- Exact rational interval input020. -/
def input020 : IntervalRat :=
  ⟨(q
    41
    1024),
    (q
    103
    2560), by certificate_kernel⟩

/-- Exact rational interval sin020. -/
def sin020 : IntervalRat :=
  ⟨(q
    5494390817699296599533669429011549904913217
    137262791555962964880814893957120000000000000),
    (q
    16563621465811003295437788277794620045260349
    411788374667888894642444681871360000000000000), by certificate_kernel⟩

/-- Exact rational interval cos020. -/
def cos020 : IntervalRat :=
  ⟨(q
    411455116666810636363037028305532994539439651
    411788374667888894642444681871360000000000000),
    (q
    1234375034278340723346441673303811000898906047
    1235365124003666683927334045614080000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin020_eq : IntervalRat.sinComputable input020 10 = sin020 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos020_eq : IntervalRat.cosComputable input020 10 = cos020 := by
  certificate_kernel

/-- Exact rational interval input021. -/
def input021 : IntervalRat :=
  ⟨(q
    201
    5120),
    (q
    403
    10240), by certificate_kernel⟩

/-- Exact rational interval sin021. -/
def sin021 : IntervalRat :=
  ⟨(q
    203361727284386073949042725464190739277393685319253
    5181496881069075187063152896855318200320000000000000),
    (q
    203867863146484937878045817766715317893306520760747
    5181496881069075187063152896855318200320000000000000), by certificate_kernel⟩

/-- Exact rational interval cos021. -/
def cos021 : IntervalRat :=
  ⟨(q
    5177484708108837129835130907194065562709403623198293
    5181496881069075187063152896855318200320000000000000),
    (q
    5177504597487465469520304306642874777447590472642987
    5181496881069075187063152896855318200320000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin021_eq : IntervalRat.sinComputable input021 10 = sin021 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos021_eq : IntervalRat.cosComputable input021 10 = cos021 := by
  certificate_kernel

/-- Exact rational interval input022. -/
def input022 : IntervalRat :=
  ⟨(q
    201
    5120),
    (q
    1609
    40960), by certificate_kernel⟩

/-- Exact rational interval sin022. -/
def sin022 : IntervalRat :=
  ⟨(q
    852961725129259130481874048504810420530120031631935530791
    21732773094255546333399730447891848548874977280000000000000),
    (q
    853492446792688267315711663205415000875209853026596821209
    21732773094255546333399730447891848548874977280000000000000), by certificate_kernel⟩

/-- Exact rational interval cos022. -/
def cos022 : IntervalRat :=
  ⟨(q
    21716007399128005329440384198249786669399407493202507982631
    21732773094255546333399730447891848548874977280000000000000),
    (q
    21716028235222475972749236822041845939382651645245641726169
    21732773094255546333399730447891848548874977280000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin022_eq : IntervalRat.sinComputable input022 10 = sin022 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos022_eq : IntervalRat.cosComputable input022 10 = cos022 := by
  certificate_kernel

/-- Exact rational interval input023. -/
def input023 : IntervalRat :=
  ⟨(q
    1609
    40960),
    (q
    161
    4096), by certificate_kernel⟩

/-- Exact rational interval sin023. -/
def sin023 : IntervalRat :=
  ⟨(q
    84671815576031308672079148971804947925097769873
    2156029076811066104503941512687683387785216000000),
    (q
    50834679930920725113042183723080048316026090153
    1293617446086639662702364907612610032671129600000), by certificate_kernel⟩

/-- Exact rational interval cos023. -/
def cos023 : IntervalRat :=
  ⟨(q
    19389273710214156338526413529115302202534283414297
    19404261691299594940535473614189150490066944000000),
    (q
    161577436045298127779232641384215645683574936080581
    161702180760829957837795613451576254083891200000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin023_eq : IntervalRat.sinComputable input023 10 = sin023 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos023_eq : IntervalRat.cosComputable input023 10 = cos023 := by
  certificate_kernel

/-- Exact rational interval input024. -/
def input024 : IntervalRat :=
  ⟨(q
    13
    320),
    (q
    21
    512), by certificate_kernel⟩

/-- Exact rational interval sin024. -/
def sin024 : IntervalRat :=
  ⟨(q
    1132645089795438496251581798341468501
    27888313205021046832927470518272000000),
    (q
    228708397546014656542320430045188847
    5577662641004209366585494103654400000), by certificate_kernel⟩

/-- Exact rational interval cos024. -/
def cos024 : IntervalRat :=
  ⟨(q
    27864858434474474892594258360078491989
    27888313205021046832927470518272000000),
    (q
    696632578143784788060087866845157260979
    697207830125526170823186762956800000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin024_eq : IntervalRat.sinComputable input024 10 = sin024 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos024_eq : IntervalRat.cosComputable input024 10 = cos024 := by
  certificate_kernel

/-- Exact rational interval input025. -/
def input025 : IntervalRat :=
  ⟨(q
    21
    512),
    (q
    53
    1280), by certificate_kernel⟩

/-- Exact rational interval sin025. -/
def sin025 : IntervalRat :=
  ⟨(q
    24733786780776137648644719812107427808403
    603205626954915373011393576960000000000000),
    (q
    24969480678873956378342432557633692191597
    603205626954915373011393576960000000000000), by certificate_kernel⟩

/-- Exact rational interval cos025. -/
def cos025 : IntervalRat :=
  ⟨(q
    602688608192434169105455355705063250858403
    603205626954915373011393576960000000000000),
    (q
    602698318610243250762606614963720606254097
    603205626954915373011393576960000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin025_eq : IntervalRat.sinComputable input025 10 = sin025 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos025_eq : IntervalRat.cosComputable input025 10 = cos025 := by
  certificate_kernel

/-- Exact rational interval input026. -/
def input026 : IntervalRat :=
  ⟨(q
    3
    80),
    (q
    5
    128), by certificate_kernel⟩

/-- Exact rational interval sin026. -/
def sin026 : IntervalRat :=
  ⟨(q
    9045783519254455236583109275
    241282250781966149204557430784),
    (q
    235571977117927271511655780061
    6032056269549153730113935769600), by certificate_kernel⟩

/-- Exact rational interval cos026. -/
def cos026 : IntervalRat :=
  ⟨(q
    172212991860516330324856920833
    172344464844261535146112450560),
    (q
    150695387981680110797327891067797
    150801406738728843252848394240000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin026_eq : IntervalRat.sinComputable input026 10 = sin026 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos026_eq : IntervalRat.cosComputable input026 10 = cos026 := by
  certificate_kernel

/-- Exact rational interval input027. -/
def input027 : IntervalRat :=
  ⟨(q
    3211
    81920),
    (q
    803
    20480), by certificate_kernel⟩

/-- Exact rational interval sin027. -/
def sin027 : IntervalRat :=
  ⟨(q
    12601154402358967394577501410900485027607761285531141
    321566836740286847972889004023020959825920000000000000),
    (q
    12605080784324102158005773433780426607330625805924859
    321566836740286847972889004023020959825920000000000000), by certificate_kernel⟩

/-- Exact rational interval cos027. -/
def cos027 : IntervalRat :=
  ⟨(q
    107106562962938895598819141321209559087708850186607367
    107188945580095615990963001341006986608640000000000000),
    (q
    240989882081161511975482077847198619761878488953613093
    241175127555215135979666753017265719869440000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin027_eq : IntervalRat.sinComputable input027 10 = sin027 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos027_eq : IntervalRat.cosComputable input027 10 = cos027 := by
  certificate_kernel

/-- Exact rational interval input028. -/
def input028 : IntervalRat :=
  ⟨(q
    3211
    81920),
    (q
    6423
    163840), by certificate_kernel⟩

/-- Exact rational interval sin028. -/
def sin028 : IntervalRat :=
  ⟨(q
    44099041040380984138711764138616875230098335145102964652441833
    1125356260744795247016837321191537925135068058091520000000000000),
    (q
    44105911429123751918024273318633717072387964993900947211878167
    1125356260744795247016837321191537925135068058091520000000000000), by certificate_kernel⟩

/-- Exact rational interval cos028. -/
def cos028 : IntervalRat :=
  ⟨(q
    1124491610643365452710298289350326158189175471086730956420874473
    1125356260744795247016837321191537925135068058091520000000000000),
    (q
    160641697127495801375370059076631257490599822609041702889202801
    160765180106399321002405331598791132162152579727360000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin028_eq : IntervalRat.sinComputable input028 10 = sin028 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos028_eq : IntervalRat.cosComputable input028 10 = cos028 := by
  certificate_kernel

/-- Exact rational interval input029. -/
def input029 : IntervalRat :=
  ⟨(q
    6423
    163840),
    (q
    803
    20480), by certificate_kernel⟩

/-- Exact rational interval sin029. -/
def sin029 : IntervalRat :=
  ⟨(q
    37809349763398285002012891815761847383444391721041423
    964700510220860543918667012069062879477760000000000000),
    (q
    37815239336580871302378242782050988822038547605294577
    964700510220860543918667012069062879477760000000000000), by certificate_kernel⟩

/-- Exact rational interval cos029. -/
def cos029 : IntervalRat :=
  ⟨(q
    481979533348009114557671135642382751330517633200330489
    482350255110430271959333506034531439738880000000000000),
    (q
    61693395042757450926046778455701520296837300735140685883
    61740832654135074810794688772420024286576640000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin029_eq : IntervalRat.sinComputable input029 10 = sin029 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos029_eq : IntervalRat.cosComputable input029 10 = cos029 := by
  certificate_kernel

/-- Exact rational interval input030. -/
def input030 : IntervalRat :=
  ⟨(q
    6421
    163840),
    (q
    3211
    81920), by certificate_kernel⟩

/-- Exact rational interval sin030. -/
def sin030 : IntervalRat :=
  ⟨(q
    581293358176851566709008340967146536469854107948918921442063
    14836239765678452963600882652427501942698651156480000000000000),
    (q
    83054847797674059905773660519409283471578569404380363889991
    2119462823668350423371554664632500277528378736640000000000000), by certificate_kernel⟩

/-- Exact rational interval cos030. -/
def cos030 : IntervalRat :=
  ⟨(q
    44474532356301895860013131723758340293468556771581009115553069
    44508719297035358890802647957282505828095953469440000000000000),
    (q
    14824847667885425541064810591036254614521972211519129620436977
    14836239765678452963600882652427501942698651156480000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin030_eq : IntervalRat.sinComputable input030 10 = sin030 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos030_eq : IntervalRat.cosComputable input030 10 = cos030 := by
  certificate_kernel

/-- Exact rational interval input031. -/
def input031 : IntervalRat :=
  ⟨(q
    5
    128),
    (q
    51
    1280), by certificate_kernel⟩

/-- Exact rational interval sin031. -/
def sin031 : IntervalRat :=
  ⟨(q
    41545830475715126298376514423253600947
    1063854721260873673741434880000000000000),
    (q
    42377182589799834911421424776746399053
    1063854721260873673741434880000000000000), by certificate_kernel⟩

/-- Exact rational interval cos031. -/
def cos031 : IntervalRat :=
  ⟨(q
    7441072666725300214870879419434775206629
    7446983048826115716190044160000000000000),
    (q
    7441302203252702704225404140637224793371
    7446983048826115716190044160000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin031_eq : IntervalRat.sinComputable input031 10 = sin031 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos031_eq : IntervalRat.cosComputable input031 10 = cos031 := by
  certificate_kernel

/-- Exact rational interval input032. -/
def input032 : IntervalRat :=
  ⟨(q
    803
    20480),
    (q
    1607
    40960), by certificate_kernel⟩

/-- Exact rational interval sin032. -/
def sin032 : IntervalRat :=
  ⟨(q
    10517300887030309845653337382823429760753984052103739097
    268305840669821559671601610467800599368826880000000000000),
    (q
    31571559006441249139499610110905747057644199055286606709
    804917522009464679014804831403401798106480640000000000000), by certificate_kernel⟩

/-- Exact rational interval cos032. -/
def cos032 : IntervalRat :=
  ⟨(q
    3102292721096146790914345409943381095573125265251501409231
    3104681870607935190485675778270264078410711040000000000000),
    (q
    7238689952620004306919486169166541226493778751886295103261
    7244257698085182111133243482630616182958325760000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin032_eq : IntervalRat.sinComputable input032 10 = sin032 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos032_eq : IntervalRat.cosComputable input032 10 = cos032 := by
  certificate_kernel

/-- Exact rational interval input033. -/
def input033 : IntervalRat :=
  ⟨(q
    321
    8192),
    (q
    3211
    81920), by certificate_kernel⟩

/-- Exact rational interval sin033. -/
def sin033 : IntervalRat :=
  ⟨(q
    1743608484413265342387086370911585735204378577336332651174189
    44508719297035358890802647957282505828095953469440000000000000),
    (q
    1744151942832799345887373421740562616581730115064368788825811
    44508719297035358890802647957282505828095953469440000000000000), by certificate_kernel⟩

/-- Exact rational interval cos033. -/
def cos033 : IntervalRat :=
  ⟨(q
    44474532354938972903448810572853812770771709895201476151974189
    44508719297035358890802647957282505828095953469440000000000000),
    (q
    44474553647989655373529531899841241031147972714608545428825811
    44508719297035358890802647957282505828095953469440000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin033_eq : IntervalRat.sinComputable input033 10 = sin033 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos033_eq : IntervalRat.cosComputable input033 10 = cos033 := by
  certificate_kernel

/-- Exact rational interval input034. -/
def input034 : IntervalRat :=
  ⟨(q
    321
    8192),
    (q
    6421
    163840), by certificate_kernel⟩

/-- Exact rational interval sin034. -/
def sin034 : IntervalRat :=
  ⟨(q
    3570910460873231023876887612671542876775214603017358742197307379
    91153857120328415008363823016514571935940512705413120000000000000),
    (q
    3571466962272653630733924980863215748398161550512475794762692621
    91153857120328415008363823016514571935940512705413120000000000000), by certificate_kernel⟩

/-- Exact rational interval cos034. -/
def cos034 : IntervalRat :=
  ⟨(q
    91083864065906825827479365252899809383062399387985223920718907379
    91153857120328415008363823016514571935940512705413120000000000000),
    (q
    13011983695470407389034090514074604786694312773728542831663241803
    13021979588618345001194831859502081705134358957916160000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin034_eq : IntervalRat.sinComputable input034 10 = sin034 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos034_eq : IntervalRat.cosComputable input034 10 = cos034 := by
  certificate_kernel

/-- Exact rational interval input035. -/
def input035 : IntervalRat :=
  ⟨(q
    403
    10240),
    (q
    807
    20480), by certificate_kernel⟩

/-- Exact rational interval sin035. -/
def sin035 : IntervalRat :=
  ⟨(q
    5154575083287692715506174491689492523081738966442297
    131008711264561308433399223861230761410560000000000000),
    (q
    5160973646506438987568393023601237432164631489109703
    131008711264561308433399223861230761410560000000000000), by certificate_kernel⟩

/-- Exact rational interval cos035. -/
def cos035 : IntervalRat :=
  ⟨(q
    130907015869426183821293036284496188937511085056958777
    131008711264561308433399223861230761410560000000000000),
    (q
    18701038254140483566065637212674652441986852554439489
    18715530180651615490485603408747251630080000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin035_eq : IntervalRat.sinComputable input035 10 = sin035 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos035_eq : IntervalRat.cosComputable input035 10 = cos035 := by
  certificate_kernel

/-- Exact rational interval input036. -/
def input036 : IntervalRat :=
  ⟨(q
    807
    20480),
    (q
    101
    2560), by certificate_kernel⟩

/-- Exact rational interval sin036. -/
def sin036 : IntervalRat :=
  ⟨(q
    48666066612946314334891845232009760229002899
    1235365124003666683927334045614080000000000000),
    (q
    6960914686591748414742511344509784724932443
    176480732000523811989619149373440000000000000), by certificate_kernel⟩

/-- Exact rational interval cos036. -/
def cos036 : IntervalRat :=
  ⟨(q
    9875230361458374221186076790594864538534328137
    9882920992029333471418672364912640000000000000),
    (q
    632015960854703540535213519648501159510585947017
    632506943489877342170795031354408960000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin036_eq : IntervalRat.sinComputable input036 10 = sin036 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos036_eq : IntervalRat.cosComputable input036 10 = cos036 := by
  certificate_kernel

/-- Exact rational interval input037. -/
def input037 : IntervalRat :=
  ⟨(q
    5
    128),
    (q
    101
    2560), by certificate_kernel⟩

/-- Exact rational interval sin037. -/
def sin037 : IntervalRat :=
  ⟨(q
    16081310729785166166494046089387382278149633
    411788374667888894642444681871360000000000000),
    (q
    2320315269056901151470564743202031103121481
    58826910666841270663206383124480000000000000), by certificate_kernel⟩

/-- Exact rational interval cos037. -/
def cos037 : IntervalRat :=
  ⟨(q
    1234403793033583877659203370949621090834448899
    1235365124003666683927334045614080000000000000),
    (q
    411474245820143472203155001134830217721850367
    411788374667888894642444681871360000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin037_eq : IntervalRat.sinComputable input037 10 = sin037 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos037_eq : IntervalRat.cosComputable input037 10 = cos037 := by
  certificate_kernel

/-- Exact rational interval input038. -/
def input038 : IntervalRat :=
  ⟨(q
    3
    64),
    (q
    1
    20), by certificate_kernel⟩

/-- Exact rational interval sin038. -/
def sin038 : IntervalRat :=
  ⟨(q
    12551508142998106644107857
    267877110251520000000000000),
    (q
    836809446830123319611423
    16742319390720000000000000), by certificate_kernel⟩

/-- Exact rational interval cos038. -/
def cos038 : IntervalRat :=
  ⟨(q
    133771162585400625034699241
    133938555125760000000000000),
    (q
    4892943962993268305739672847
    4898324301742080000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin038_eq : IntervalRat.sinComputable input038 10 = sin038 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos038_eq : IntervalRat.cosComputable input038 10 = cos038 := by
  certificate_kernel

/-- Exact rational interval input039. -/
def input039 : IntervalRat :=
  ⟨(q
    5
    128),
    (q
    201
    5120), by certificate_kernel⟩

/-- Exact rational interval sin039. -/
def sin039 : IntervalRat :=
  ⟨(q
    1219800325002194592765980943135119234946639479
    31234910789623572452878766980464640000000000000),
    (q
    1225902452847426393011616468566435965053360521
    31234910789623572452878766980464640000000000000), by certificate_kernel⟩

/-- Exact rational interval cos039. -/
def cos039 : IntervalRat :=
  ⟨(q
    31210844605056664047003750262841816962946639479
    31234910789623572452878766980464640000000000000),
    (q
    31211083504274430963225992488432855165053360521
    31234910789623572452878766980464640000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin039_eq : IntervalRat.sinComputable input039 10 = sin039 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos039_eq : IntervalRat.cosComputable input039 10 = cos039 := by
  certificate_kernel

/-- Exact rational interval input040. -/
def input040 : IntervalRat :=
  ⟨(q
    401
    10240),
    (q
    321
    8192), by certificate_kernel⟩

/-- Exact rational interval sin040. -/
def sin040 : IntervalRat :=
  ⟨(q
    134453889033120603141029509380760908425910474625567
    3434314760573715963796500613987847671920984064000000),
    (q
    26907551210623251100949241476436101245875128240429
    686862952114743192759300122797569534384196812800000), by certificate_kernel⟩

/-- Exact rational interval cos040. -/
def cos040 : IntervalRat :=
  ⟨(q
    3431678521590981430082767794451734277709204347802143
    3434314760573715963796500613987847671920984064000000),
    (q
    85792045150508363424750360166708448878326199885658873
    85857869014342899094912515349696191798024601600000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin040_eq : IntervalRat.sinComputable input040 10 = sin040 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos040_eq : IntervalRat.cosComputable input040 10 = cos040 := by
  certificate_kernel

/-- Exact rational interval input041. -/
def input041 : IntervalRat :=
  ⟨(q
    5
    128),
    (q
    401
    10240), by certificate_kernel⟩

/-- Exact rational interval sin041. -/
def sin041 : IntervalRat :=
  ⟨(q
    9635737839386639840530872322934103682279115771219
    246737946717575008907769185564538961920000000000000),
    (q
    9659839485588352362039093500842103984920884228781
    246737946717575008907769185564538961920000000000000), by certificate_kernel⟩

/-- Exact rational interval cos041. -/
def cos041 : IntervalRat :=
  ⟨(q
    5177524427285008069753371566162594656988917431195599
    5181496881069075187063152896855318200320000000000000),
    (q
    575282690870491471667086161174204215367482063200489
    575721875674341687451461432983924244480000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin041_eq : IntervalRat.sinComputable input041 10 = sin041 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos041_eq : IntervalRat.cosComputable input041 10 = cos041 := by
  certificate_kernel

/-- Exact rational interval input042. -/
def input042 : IntervalRat :=
  ⟨(q
    401
    10240),
    (q
    803
    20480), by certificate_kernel⟩

/-- Exact rational interval sin042. -/
def sin042 : IntervalRat :=
  ⟨(q
    12589381289716959486479911003926870505746585411995141
    321566836740286847972889004023020959825920000000000000),
    (q
    12605086813819352371506196225263676697626751737444859
    321566836740286847972889004023020959825920000000000000), by certificate_kernel⟩

/-- Exact rational interval cos042. -/
def cos042 : IntervalRat :=
  ⟨(q
    321319688829712576231593300911930006674483971074704901
    321566836740286847972889004023020959825920000000000000),
    (q
    963960912259412182072706018303796361706860316441718257
    964700510220860543918667012069062879477760000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin042_eq : IntervalRat.sinComputable input042 10 = sin042 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos042_eq : IntervalRat.cosComputable input042 10 = cos042 := by
  certificate_kernel

/-- Exact rational interval input043. -/
def input043 : IntervalRat :=
  ⟨(q
    3
    80),
    (q
    49
    1280), by certificate_kernel⟩

/-- Exact rational interval sin043. -/
def sin043 : IntervalRat :=
  ⟨(q
    3230669512251222173985930960469637291993
    86172232422130767573056225280000000000000),
    (q
    3298007677315182853245650733664159572007
    86172232422130767573056225280000000000000), by certificate_kernel⟩

/-- Exact rational interval cos043. -/
def cos043 : IntervalRat :=
  ⟨(q
    86109099095351223226542931284489770196953
    86172232422130767573056225280000000000000),
    (q
    86111649970165919123664800895114098679847
    86172232422130767573056225280000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin043_eq : IntervalRat.sinComputable input043 10 = sin043 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos043_eq : IntervalRat.cosComputable input043 10 = cos043 := by
  certificate_kernel

/-- Exact rational interval input044. -/
def input044 : IntervalRat :=
  ⟨(q
    51
    1280),
    (q
    13
    320), by certificate_kernel⟩

/-- Exact rational interval sin044. -/
def sin044 : IntervalRat :=
  ⟨(q
    818367134370005781051199747246709
    20545061212094013112320000000000000),
    (q
    5840956057377688189975235465286037
    143815428484658091786240000000000000), by certificate_kernel⟩

/-- Exact rational interval cos044. -/
def cos044 : IntervalRat :=
  ⟨(q
    82112439066518182679175654871865051
    82180244848376052449280000000000000),
    (q
    9196882491646163938264590489074458513
    9204187423018117874319360000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin044_eq : IntervalRat.sinComputable input044 10 = sin044 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos044_eq : IntervalRat.cosComputable input044 10 = cos044 := by
  certificate_kernel

/-- Exact rational interval input045. -/
def input045 : IntervalRat :=
  ⟨(q
    49
    1280),
    (q
    99
    2560), by certificate_kernel⟩

/-- Exact rational interval sin045. -/
def sin045 : IntervalRat :=
  ⟨(q
    53063450668296993415734599470763252558111
    1386492843999625907887019130880000000000000),
    (q
    53605183076541675369280812955342693553889
    1386492843999625907887019130880000000000000), by certificate_kernel⟩

/-- Exact rational interval cos045. -/
def cos045 : IntervalRat :=
  ⟨(q
    1385456210932295119876947354892457887729951
    1386492843999625907887019130880000000000000),
    (q
    1385477049791237589794359097692358219585249
    1386492843999625907887019130880000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin045_eq : IntervalRat.sinComputable input045 10 = sin045 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos045_eq : IntervalRat.cosComputable input045 10 = cos045 := by
  certificate_kernel

/-- Exact rational interval input046. -/
def input046 : IntervalRat :=
  ⟨(q
    101
    2560),
    (q
    51
    1280), by certificate_kernel⟩

/-- Exact rational interval sin046. -/
def sin046 : IntervalRat :=
  ⟨(q
    293729021582512639273396332973799078629
    7446983048826115716190044160000000000000),
    (q
    296638761528860741941483474507438937371
    7446983048826115716190044160000000000000), by certificate_kernel⟩

/-- Exact rational interval cos046. -/
def cos046 : IntervalRat :=
  ⟨(q
    7441072681832455112060059985955889148149
    7446983048826115716190044160000000000000),
    (q
    1063026859750841892737552240091807932393
    1063854721260873673741434880000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin046_eq : IntervalRat.sinComputable input046 10 = sin046 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos046_eq : IntervalRat.cosComputable input046 10 = cos046 := by
  certificate_kernel

/-- Exact rational interval input047. -/
def input047 : IntervalRat :=
  ⟨(q
    1
    32),
    (q
    11
    320), by certificate_kernel⟩

/-- Exact rational interval sin047. -/
def sin047 : IntervalRat :=
  ⟨(q
    136162032994425065519539087525133
    4358043287413881569280000000000000),
    (q
    149783356675544693891937392474867
    4358043287413881569280000000000000), by certificate_kernel⟩

/-- Exact rational interval cos047. -/
def cos047 : IntervalRat :=
  ⟨(q
    4355468676448098436416866489125133
    4358043287413881569280000000000000),
    (q
    1866820948338238573851245716774943
    1867732837463092101120000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin047_eq : IntervalRat.sinComputable input047 10 = sin047 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos047_eq : IntervalRat.cosComputable input047 10 = cos047 := by
  certificate_kernel

/-- Exact rational interval input048. -/
def input048 : IntervalRat :=
  ⟨(q
    401
    10240),
    (q
    3209
    81920), by certificate_kernel⟩

/-- Exact rational interval sin048. -/
def sin048 : IntervalRat :=
  ⟨(q
    82977270462274318134809550488512967797946301874329794981771
    2119462823668350423371554664632500277528378736640000000000000),
    (q
    581022045984679592666988406316251503508393150047174585463603
    14836239765678452963600882652427501942698651156480000000000000), by certificate_kernel⟩

/-- Exact rational interval cos048. -/
def cos048 : IntervalRat :=
  ⟨(q
    705945633706624859038903110523504619795589830237033682374617
    706487607889450141123851554877500092509459578880000000000000),
    (q
    44474596203303416139932019710086939478855242110166883990968729
    44508719297035358890802647957282505828095953469440000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin048_eq : IntervalRat.sinComputable input048 10 = sin048 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos048_eq : IntervalRat.cosComputable input048 10 = cos048 := by
  certificate_kernel

/-- Exact rational interval input049. -/
def input049 : IntervalRat :=
  ⟨(q
    13
    320),
    (q
    27
    640), by certificate_kernel⟩

/-- Exact rational interval sin049. -/
def sin049 : IntervalRat :=
  ⟨(q
    147677711394650259591611009567851117
    3636222191809626814545920000000000000),
    (q
    153360931625593419503814820066196883
    3636222191809626814545920000000000000), by certificate_kernel⟩

/-- Exact rational interval cos049. -/
def cos049 : IntervalRat :=
  ⟨(q
    3632986789676636043478438191564917357
    3636222191809626814545920000000000000),
    (q
    3633222043311570570826365239704919443
    3636222191809626814545920000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin049_eq : IntervalRat.sinComputable input049 10 = sin049 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos049_eq : IntervalRat.cosComputable input049 10 = cos049 := by
  certificate_kernel

/-- Exact rational interval input050. -/
def input050 : IntervalRat :=
  ⟨(q
    803
    20480),
    (q
    201
    5120), by certificate_kernel⟩

/-- Exact rational interval sin050. -/
def sin050 : IntervalRat :=
  ⟨(q
    1224374576401286046151925974324123595863887479
    31234910789623572452878766980464640000000000000),
    (q
    1225900109824579912260911026792282241775024521
    31234910789623572452878766980464640000000000000), by certificate_kernel⟩

/-- Exact rational interval cos050. -/
def cos050 : IntervalRat :=
  ⟨(q
    31210844628052742593660424353691201195489127259
    31234910789623572452878766980464640000000000000),
    (q
    124843617858247734887398291380913650538216333589
    124939643158494289811515067921858560000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin050_eq : IntervalRat.sinComputable input050 10 = sin050 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos050_eq : IntervalRat.cosComputable input050 10 = cos050 := by
  certificate_kernel

/-- Exact rational interval input051. -/
def input051 : IntervalRat :=
  ⟨(q
    5
    128),
    (q
    801
    20480), by certificate_kernel⟩

/-- Exact rational interval sin051. -/
def sin051 : IntervalRat :=
  ⟨(q
    5116223173023498245844513292553025822851829475120879
    131008711264561308433399223861230761410560000000000000),
    (q
    731803101675633954216522698708515265604938646411303
    18715530180651615490485603408747251630080000000000000), by certificate_kernel⟩

/-- Exact rational interval cos051. -/
def cos051 : IntervalRat :=
  ⟨(q
    130908522255235371629531702599743690917741301475120879
    131008711264561308433399223861230761410560000000000000),
    (q
    130908772290697863720344490949388671416597770524879121
    131008711264561308433399223861230761410560000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin051_eq : IntervalRat.sinComputable input051 10 = sin051 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos051_eq : IntervalRat.cosComputable input051 10 = cos051 := by
  certificate_kernel

/-- Exact rational interval input052. -/
def input052 : IntervalRat :=
  ⟨(q
    5
    128),
    (q
    13
    320), by certificate_kernel⟩

/-- Exact rational interval sin052. -/
def sin052 : IntervalRat :=
  ⟨(q
    208009075371534579388705382948369
    5326497351283633029120000000000000),
    (q
    1947005359918723731085389053464679
    47938476161552697262080000000000000), by certificate_kernel⟩

/-- Exact rational interval cos052. -/
def cos052 : IntervalRat :=
  ⟨(q
    143696767756787770669938283941168463
    143815428484658091786240000000000000),
    (q
    23950953518323683001988380439818277
    23969238080776348631040000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin052_eq : IntervalRat.sinComputable input052 10 = sin052 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos052_eq : IntervalRat.cosComputable input052 10 = cos052 := by
  certificate_kernel

/-- Exact rational interval input053. -/
def input053 : IntervalRat :=
  ⟨(q
    99
    2560),
    (q
    199
    5120), by certificate_kernel⟩

/-- Exact rational interval sin053. -/
def sin053 : IntervalRat :=
  ⟨(q
    97816285631204446173753733405981259965671509801
    2530027773959509368683180125417635840000000000000),
    (q
    98310555479214168462356623239682386365241258199
    2530027773959509368683180125417635840000000000000), by certificate_kernel⟩

/-- Exact rational interval cos053. -/
def cos053 : IntervalRat :=
  ⟨(q
    2528117008425923774554518883357414286800921808681
    2530027773959509368683180125417635840000000000000),
    (q
    2528136166236756089128753923471827883884202389719
    2530027773959509368683180125417635840000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin053_eq : IntervalRat.sinComputable input053 10 = sin053 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos053_eq : IntervalRat.cosComputable input053 10 = cos053 := by
  certificate_kernel

/-- Exact rational interval input054. -/
def input054 : IntervalRat :=
  ⟨(q
    3209
    81920),
    (q
    6419
    163840), by certificate_kernel⟩

/-- Exact rational interval sin054. -/
def sin054 : IntervalRat :=
  ⟨(q
    169990409378259043923134901846231026121492451547179135742036161
    4340659862872781667064943953167360568378119652638720000000000000),
    (q
    170016909440673742540861876687936620699156375791173138698155839
    4340659862872781667064943953167360568378119652638720000000000000), by certificate_kernel⟩

/-- Exact rational interval cos054. -/
def cos054 : IntervalRat :=
  ⟨(q
    13011986808018356422131424855108937221971087908804119651539114563
    13021979588618345001194831859502081705134358957916160000000000000),
    (q
    4337329973891572811257858128975306149025723219597304447149750079
    4340659862872781667064943953167360568378119652638720000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin054_eq : IntervalRat.sinComputable input054 10 = sin054 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos054_eq : IntervalRat.cosComputable input054 10 = cos054 := by
  certificate_kernel

/-- Exact rational interval input055. -/
def input055 : IntervalRat :=
  ⟨(q
    201
    5120),
    (q
    101
    2560), by certificate_kernel⟩

/-- Exact rational interval sin055. -/
def sin055 : IntervalRat :=
  ⟨(q
    48485151859924852207507779638918510325776899
    1235365124003666683927334045614080000000000000),
    (q
    48726496400266752885976108494535143348207101
    1235365124003666683927334045614080000000000000), by certificate_kernel⟩

/-- Exact rational interval cos055. -/
def cos055 : IntervalRat :=
  ⟨(q
    1234403794259127656322426607237315517983023139
    1235365124003666683927334045614080000000000000),
    (q
    1234413290035271512230811409824354262017486661
    1235365124003666683927334045614080000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin055_eq : IntervalRat.sinComputable input055 10 = sin055 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos055_eq : IntervalRat.cosComputable input055 10 = cos055 := by
  certificate_kernel

/-- Exact rational interval input056. -/
def input056 : IntervalRat :=
  ⟨(q
    321
    8192),
    (q
    803
    20480), by certificate_kernel⟩

/-- Exact rational interval sin056. -/
def sin056 : IntervalRat :=
  ⟨(q
    37791690094434461355381730108488907273831074014417423
    964700510220860543918667012069062879477760000000000000),
    (q
    37815248384346196761666578694315231681013577505582577
    964700510220860543918667012069062879477760000000000000), by certificate_kernel⟩

/-- Exact rational interval cos056. -/
def cos056 : IntervalRat :=
  ⟨(q
    963959066607327534460464839642858300480932656535217423
    964700510220860543918667012069062879477760000000000000),
    (q
    963959989779967926704503185423581937702334781580582577
    964700510220860543918667012069062879477760000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin056_eq : IntervalRat.sinComputable input056 10 = sin056 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos056_eq : IntervalRat.cosComputable input056 10 = cos056 := by
  certificate_kernel

/-- Exact rational interval input057. -/
def input057 : IntervalRat :=
  ⟨(q
    49
    1280),
    (q
    5
    128), by certificate_kernel⟩

/-- Exact rational interval sin057. -/
def sin057 : IntervalRat :=
  ⟨(q
    76951977912712350686693389409
    2010685423183051243371311923200),
    (q
    78523217426401986231661574047
    2010685423183051243371311923200), by certificate_kernel⟩

/-- Exact rational interval cos057. -/
def cos057 : IntervalRat :=
  ⟨(q
    133943438618270045865868459159
    134045694878870082891420794880),
    (q
    150690924518356495176900213358783
    150801406738728843252848394240000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin057_eq : IntervalRat.sinComputable input057 10 = sin057 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos057_eq : IntervalRat.cosComputable input057 10 = cos057 := by
  certificate_kernel

/-- Exact rational interval input058. -/
def input058 : IntervalRat :=
  ⟨(q
    1
    40),
    (q
    1
    32), by certificate_kernel⟩

/-- Exact rational interval sin058. -/
def sin058 : IntervalRat :=
  ⟨(q
    7489167799846922991522949
    299615476009704357888000000),
    (q
    1872401672426169495803263
    59923095201940871577600000), by certificate_kernel⟩

/-- Exact rational interval cos058. -/
def cos058 : IntervalRat :=
  ⟨(q
    898407561029779629979639183
    898846428029113073664000000),
    (q
    2496015448274234721173345537
    2496795633414202982400000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin058_eq : IntervalRat.sinComputable input058 10 = sin058 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos058_eq : IntervalRat.cosComputable input058 10 = cos058 := by
  certificate_kernel

/-- Exact rational interval input059. -/
def input059 : IntervalRat :=
  ⟨(q
    99
    2560),
    (q
    5
    128), by certificate_kernel⟩

/-- Exact rational interval sin059. -/
def sin059 : IntervalRat :=
  ⟨(q
    46642321324108665380561670311
    1206411253909830746022787153920),
    (q
    235568471884287987322464063581
    6032056269549153730113935769600), by certificate_kernel⟩

/-- Exact rational interval cos059. -/
def cos059 : IntervalRat :=
  ⟨(q
    2410981899739895732156428127527
    2412822507819661492045574307840),
    (q
    688862437830306157694705996261707
    689377859377046140584449802240000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin059_eq : IntervalRat.sinComputable input059 10 = sin059 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos059_eq : IntervalRat.cosComputable input059 10 = cos059 := by
  certificate_kernel

/-- Exact rational interval input060. -/
def input060 : IntervalRat :=
  ⟨(q
    801
    20480),
    (q
    401
    10240), by certificate_kernel⟩

/-- Exact rational interval sin060. -/
def sin060 : IntervalRat :=
  ⟨(q
    202603432755288433540214186916795469898438278043599
    5181496881069075187063152896855318200320000000000000),
    (q
    202856500121047242556812005975351888738685977700401
    5181496881069075187063152896855318200320000000000000), by certificate_kernel⟩

/-- Exact rational interval cos060. -/
def cos060 : IntervalRat :=
  ⟨(q
    5177524428548702465078679482313396757443195474324559
    5181496881069075187063152896855318200320000000000000),
    (q
    739647761428605124838221554226139452841433614642663
    740213840152725026723307556693616885760000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin060_eq : IntervalRat.sinComputable input060 10 = sin060 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos060_eq : IntervalRat.cosComputable input060 10 = cos060 := by
  certificate_kernel

/-- Exact rational interval input061. -/
def input061 : IntervalRat :=
  ⟨(q
    3209
    81920),
    (q
    321
    8192), by certificate_kernel⟩

/-- Exact rational interval sin061. -/
def sin061 : IntervalRat :=
  ⟨(q
    134495801094938928465570001782349399583722298790431
    3434314760573715963796500613987847671920984064000000),
    (q
    26907546921655880610390882919902154694746530777389
    686862952114743192759300122797569534384196812800000), by certificate_kernel⟩

/-- Exact rational interval cos061. -/
def cos061 : IntervalRat :=
  ⟨(q
    3431678521801063485246857552929558101315826956229663
    3434314760573715963796500613987847671920984064000000),
    (q
    85792004106790410906529616757578220593769942042117497
    85857869014342899094912515349696191798024601600000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin061_eq : IntervalRat.sinComputable input061 10 = sin061 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos061_eq : IntervalRat.cosComputable input061 10 = cos061 := by
  certificate_kernel

/-- Exact rational interval input062. -/
def input062 : IntervalRat :=
  ⟨(q
    11
    320),
    (q
    3
    80), by certificate_kernel⟩

/-- Exact rational interval sin062. -/
def sin062 : IntervalRat :=
  ⟨(q
    29095877855740828995840751
    846623953387520000000000000),
    (q
    15871073079395984082390437
    423311976693760000000000000), by certificate_kernel⟩

/-- Exact rational interval cos062. -/
def cos062 : IntervalRat :=
  ⟨(q
    6768229836280338518987597713
    6772991627100160000000000000),
    (q
    108303847599871537003725204017
    108367866033602560000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin062_eq : IntervalRat.sinComputable input062 10 = sin062 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos062_eq : IntervalRat.cosComputable input062 10 = cos062 := by
  certificate_kernel

/-- Exact rational interval input063. -/
def input063 : IntervalRat :=
  ⟨(q
    401
    10240),
    (q
    201
    5120), by certificate_kernel⟩

/-- Exact rational interval sin063. -/
def sin063 : IntervalRat :=
  ⟨(q
    174692832276385372468848397363828976921684497
    4462130112803367493268395282923520000000000000),
    (q
    1225900891806627875312159270414225079724464521
    31234910789623572452878766980464640000000000000), by certificate_kernel⟩

/-- Exact rational interval cos063. -/
def cos063 : IntervalRat :=
  ⟨(q
    4458692088625402758674817003718901465189481937
    4462130112803367493268395282923520000000000000),
    (q
    31210964218926368629467708323282222173937142041
    31234910789623572452878766980464640000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin063_eq : IntervalRat.sinComputable input063 10 = sin063 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos063_eq : IntervalRat.cosComputable input063 10 = cos063 := by
  certificate_kernel

/-- Exact rational interval input064. -/
def input064 : IntervalRat :=
  ⟨(q
    199
    5120),
    (q
    5
    128), by certificate_kernel⟩

/-- Exact rational interval sin064. -/
def sin064 : IntervalRat :=
  ⟨(q
    1627704465713632462502062657
    41889279649646900903568998400),
    (q
    78522625730979890394633986087
    2010685423183051243371311923200), by certificate_kernel⟩

/-- Exact rational interval cos064. -/
def cos064 : IntervalRat :=
  ⟨(q
    1836938592047975532920505076517
    1838340958338789708225199472640),
    (q
    308608033845375280939017691317685829
    308841281000916670981833511403520000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin064_eq : IntervalRat.sinComputable input064 10 = sin064 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos064_eq : IntervalRat.cosComputable input064 10 = cos064 := by
  certificate_kernel

/-- Exact rational interval input065. -/
def input065 : IntervalRat :=
  ⟨(q
    11
    320),
    (q
    23
    640), by certificate_kernel⟩

/-- Exact rational interval sin065. -/
def sin065 : IntervalRat :=
  ⟨(q
    1124714107334052648778010542290350897
    32725999726286641330913280000000000000),
    (q
    1175859010711614181650221446056529103
    32725999726286641330913280000000000000), by certificate_kernel⟩

/-- Exact rational interval cos065. -/
def cos065 : IntervalRat :=
  ⟨(q
    294343820360203149721571733139832214713
    294533997536579771978219520000000000000),
    (q
    98119999865325419980240238859512071789
    98177999178859923992739840000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin065_eq : IntervalRat.sinComputable input065 10 = sin065 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos065_eq : IntervalRat.cosComputable input065 10 = cos065 := by
  certificate_kernel

/-- Exact rational interval input066. -/
def input066 : IntervalRat :=
  ⟨(q
    1
    20),
    (q
    9
    160), by certificate_kernel⟩

/-- Exact rational interval sin066. -/
def sin066 : IntervalRat :=
  ⟨(q
    6189184346262878960653701073
    123848989752688640000000000000),
    (q
    6963603422081977450588794927
    123848989752688640000000000000), by certificate_kernel⟩

/-- Exact rational interval cos066. -/
def cos066 : IntervalRat :=
  ⟨(q
    865571683169782136301969632951
    866942928268820480000000000000),
    (q
    865859535320258769326943211849
    866942928268820480000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin066_eq : IntervalRat.sinComputable input066 10 = sin066 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos066_eq : IntervalRat.cosComputable input066 10 = cos066 := by
  certificate_kernel

/-- Exact rational interval input067. -/
def input067 : IntervalRat :=
  ⟨(q
    9
    160),
    (q
    1
    16), by certificate_kernel⟩

/-- Exact rational interval sin067. -/
def sin067 : IntervalRat :=
  ⟨(q
    3524497770952609989257
    62698551062298624000000),
    (q
    5483230710171126742493
    87777971487218073600000), by certificate_kernel⟩

/-- Exact rational interval cos067. -/
def cos067 : IntervalRat :=
  ⟨(q
    15644031309827467255823
    15674637765574656000000),
    (q
    43819574596379368041576649
    43888985743609036800000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin067_eq : IntervalRat.sinComputable input067 10 = sin067 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos067_eq : IntervalRat.cosComputable input067 10 = cos067 := by
  certificate_kernel

/-- Exact rational interval input068. -/
def input068 : IntervalRat :=
  ⟨(q
    6419
    163840),
    (q
    321
    8192), by certificate_kernel⟩

/-- Exact rational interval sin068. -/
def sin068 : IntervalRat :=
  ⟨(q
    134516757125848668203822633529061222462474705162783
    3434314760573715963796500613987847671920984064000000),
    (q
    26907544776670913525629123585626196028536132077869
    686862952114743192759300122797569534384196812800000), by certificate_kernel⟩

/-- Exact rational interval cos068. -/
def cos068 : IntervalRat :=
  ⟨(q
    3431678521906129066598928452438559782364780015122623
    3434314760573715963796500613987847671920984064000000),
    (q
    85791983580134366037426808777977368000770069405289843
    85857869014342899094912515349696191798024601600000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin068_eq : IntervalRat.sinComputable input068 10 = sin068 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos068_eq : IntervalRat.cosComputable input068 10 = cos068 := by
  certificate_kernel

/-- Exact rational interval input069. -/
def input069 : IntervalRat :=
  ⟨(q
    1607
    40960),
    (q
    643
    16384), by certificate_kernel⟩

/-- Exact rational interval sin069. -/
def sin069 : IntervalRat :=
  ⟨(q
    1064094531477433697434018002796247490733100376666918433
    27129124142954885419155899707296003552363247828992000000),
    (q
    70961718835668702226797637344230477170309660333695281
    1808608276196992361277059980486400236824216521932800000), by certificate_kernel⟩

/-- Exact rational interval cos069. -/
def cos069 : IntervalRat :=
  ⟨(q
    63252547041074534033047136723192416742530888168950347341
    63301289666894732644697099317024008288847578267648000000),
    (q
    14231829906507353316645465389108080343302793639857519216211
    14242790175051314845056847346330401864990705110220800000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin069_eq : IntervalRat.sinComputable input069 10 = sin069 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos069_eq : IntervalRat.cosComputable input069 10 = cos069 := by
  certificate_kernel

/-- Exact rational interval input070. -/
def input070 : IntervalRat :=
  ⟨(q
    643
    16384),
    (q
    201
    5120), by certificate_kernel⟩

/-- Exact rational interval sin070. -/
def sin070 : IntervalRat :=
  ⟨(q
    175074019893053573247167220501524415113917247
    4462130112803367493268395282923520000000000000),
    (q
    1225899522698572631850649126315788989380860521
    31234910789623572452878766980464640000000000000), by certificate_kernel⟩

/-- Exact rational interval cos070. -/
def cos070 : IntervalRat :=
  ⟨(q
    285356293794881931686483967502416565551214663183
    285576327219415519569177298107105280000000000000),
    (q
    511358723685155731842018179836568613036402713541689
    511752778377192611067965718207932661760000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin070_eq : IntervalRat.sinComputable input070 10 = sin070 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos070_eq : IntervalRat.cosComputable input070 10 = cos070 := by
  certificate_kernel

/-- Exact rational interval input071. -/
def input071 : IntervalRat :=
  ⟨(q
    801
    20480),
    (q
    1603
    40960), by certificate_kernel⟩

/-- Exact rational interval sin071. -/
def sin071 : IntervalRat :=
  ⟨(q
    121397237028081553279497237916419310675438248960757821779
    3104681870607935190485675778270264078410711040000000000000),
    (q
    121473054263479154906104734946963526540826860794900418221
    3104681870607935190485675778270264078410711040000000000000), by certificate_kernel⟩

/-- Exact rational interval cos071. -/
def cos071 : IntervalRat :=
  ⟨(q
    3102304598491087380490140353243844620484365208405632184659
    3104681870607935190485675778270264078410711040000000000000),
    (q
    3102307563972803791798879488390377272968194855752886947501
    3104681870607935190485675778270264078410711040000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin071_eq : IntervalRat.sinComputable input071 10 = sin071 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos071_eq : IntervalRat.cosComputable input071 10 = cos071 := by
  certificate_kernel

/-- Exact rational interval input072. -/
def input072 : IntervalRat :=
  ⟨(q
    1603
    40960),
    (q
    401
    10240), by certificate_kernel⟩

/-- Exact rational interval sin072. -/
def sin072 : IntervalRat :=
  ⟨(q
    7508514882199511901111187422608274399115671775837
    191907291891447229150487144327974748160000000000000),
    (q
    67618811840808811871515986375227402889889889313467
    1727165627023025062354384298951772733440000000000000), by certificate_kernel⟩

/-- Exact rational interval cos072. -/
def cos072 : IntervalRat :=
  ⟨(q
    5177524429181141649500726146611216065003813508951959
    5181496881069075187063152896855318200320000000000000),
    (q
    383520694922304800686036759984576010680477470630841
    383814583782894458300974288655949496320000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin072_eq : IntervalRat.sinComputable input072 10 = sin072 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos072_eq : IntervalRat.cosComputable input072 10 = cos072 := by
  certificate_kernel

/-- Exact rational interval input073. -/
def input073 : IntervalRat :=
  ⟨(q
    23
    640),
    (q
    3
    80), by certificate_kernel⟩

/-- Exact rational interval sin073. -/
def sin073 : IntervalRat :=
  ⟨(q
    973389369518236093893031657
    27091966508400640000000000000),
    (q
    126966259476519858095161621
    3386495813550080000000000000), by certificate_kernel⟩

/-- Exact rational interval cos073. -/
def cos073 : IntervalRat :=
  ⟨(q
    108291678078049359185351798833
    108367866033602560000000000000),
    (q
    6931065310255258569635086177913
    6935543426150563840000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin073_eq : IntervalRat.sinComputable input073 10 = sin073 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos073_eq : IntervalRat.cosComputable input073 10 = cos073 := by
  certificate_kernel

/-- Exact rational interval input074. -/
def input074 : IntervalRat :=
  ⟨(q
    199
    5120),
    (q
    399
    10240), by certificate_kernel⟩

/-- Exact rational interval sin074. -/
def sin074 : IntervalRat :=
  ⟨(q
    355095686486634419144547269144909015610135835703
    9138442471021296626213673539427368960000000000000),
    (q
    355988337782595985839546520422186629654538980297
    9138442471021296626213673539427368960000000000000), by certificate_kernel⟩

/-- Exact rational interval cos074. -/
def cos074 : IntervalRat :=
  ⟨(q
    9131506082811144729721225784899449533458333692983
    9138442471021296626213673539427368960000000000000),
    (q
    9131540812476404121210352812092274780669154921417
    9138442471021296626213673539427368960000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin074_eq : IntervalRat.sinComputable input074 10 = sin074 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos074_eq : IntervalRat.cosComputable input074 10 = cos074 := by
  certificate_kernel

/-- Exact rational interval input075. -/
def input075 : IntervalRat :=
  ⟨(q
    203
    5120),
    (q
    407
    10240), by certificate_kernel⟩

/-- Exact rational interval sin075. -/
def sin075 : IntervalRat :=
  ⟨(q
    6223762704509829648077944124238193568730641051929
    157015057002093187486762208995615703040000000000000),
    (q
    2079700077918793956765616662075169717340319521357
    52338352334031062495587402998538567680000000000000), by certificate_kernel⟩

/-- Exact rational interval cos075. -/
def cos075 : IntervalRat :=
  ⟨(q
    470673152476434187615150906452292431131468557226827
    471045171006279562460286626986847109120000000000000),
    (q
    156891659523570634202152724945068035715111100239591
    157015057002093187486762208995615703040000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin075_eq : IntervalRat.sinComputable input075 10 = sin075 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos075_eq : IntervalRat.cosComputable input075 10 = cos075 := by
  certificate_kernel

/-- Exact rational interval input076. -/
def input076 : IntervalRat :=
  ⟨(q
    407
    10240),
    (q
    51
    1280), by certificate_kernel⟩

/-- Exact rational interval sin076. -/
def sin076 : IntervalRat :=
  ⟨(q
    42272882539175140676045315455524766447
    1063854721260873673741434880000000000000),
    (q
    42376802025126730949837379196879931053
    1063854721260873673741434880000000000000), by certificate_kernel⟩

/-- Exact rational interval cos076. -/
def cos076 : IntervalRat :=
  ⟨(q
    119057163092183500035411148489980183453409
    119151728781217851459040706560000000000000),
    (q
    7619688073110813700702201242517681118010809
    7625710641997942493378605219840000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin076_eq : IntervalRat.sinComputable input076 10 = sin076 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos076_eq : IntervalRat.cosComputable input076 10 = cos076 := by
  certificate_kernel

/-- Exact rational interval input077. -/
def input077 : IntervalRat :=
  ⟨(q
    399
    10240),
    (q
    799
    20480), by certificate_kernel⟩

/-- Exact rational interval sin077. -/
def sin077 : IntervalRat :=
  ⟨(q
    413378567513691126330235891261524253965855351339383201
    10611705612429465983105337132759691674255360000000000000),
    (q
    413896848490322257896948029302495773251467288544904799
    10611705612429465983105337132759691674255360000000000000), by certificate_kernel⟩

/-- Exact rational interval cos077. -/
def cos077 : IntervalRat :=
  ⟨(q
    10603630772843801313523010277413038866993890383850338721
    10611705612429465983105337132759691674255360000000000000),
    (q
    10603650975115706061471241861722300148393632209325622879
    10611705612429465983105337132759691674255360000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin077_eq : IntervalRat.sinComputable input077 10 = sin077 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos077_eq : IntervalRat.cosComputable input077 10 = cos077 := by
  certificate_kernel

/-- Exact rational interval input078. -/
def input078 : IntervalRat :=
  ⟨(q
    5
    128),
    (q
    1601
    40960), by certificate_kernel⟩

/-- Exact rational interval sin078. -/
def sin078 : IntervalRat :=
  ⟨(q
    94302255536505206184715955471938600233124546257335464711
    2414752566028394037044414494210205394319441920000000000000),
    (q
    283083673379541718587875880114432021981516114827993605867
    7244257698085182111133243482630616182958325760000000000000), by certificate_kernel⟩

/-- Exact rational interval cos078. -/
def cos078 : IntervalRat :=
  ⟨(q
    21716173682656975419871850469952001387272257600860019182399
    21732773094255546333399730447891848548874977280000000000000),
    (q
    7238731471707168350918458585301615781064429906827993605867
    7244257698085182111133243482630616182958325760000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin078_eq : IntervalRat.sinComputable input078 10 = sin078 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos078_eq : IntervalRat.cosComputable input078 10 = cos078 := by
  certificate_kernel

/-- Exact rational interval input079. -/
def input079 : IntervalRat :=
  ⟨(q
    49
    1280),
    (q
    197
    5120), by certificate_kernel⟩

/-- Exact rational interval sin079. -/
def sin079 : IntervalRat :=
  ⟨(q
    10758747773485376554149047367238465504232441483
    281114197106612152075908902824181760000000000000),
    (q
    32440999109022986673090073224111882679628819551
    843342591319836456227726708472545280000000000000), by certificate_kernel⟩

/-- Exact rational interval cos079. -/
def cos079 : IntervalRat :=
  ⟨(q
    842718406026918965255783979446573954961921577889
    843342591319836456227726708472545280000000000000),
    (q
    2528174182865782648817083554489517109128691074333
    2530027773959509368683180125417635840000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin079_eq : IntervalRat.sinComputable input079 10 = sin079 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos079_eq : IntervalRat.cosComputable input079 10 = cos079 := by
  certificate_kernel

/-- Exact rational interval input080. -/
def input080 : IntervalRat :=
  ⟨(q
    3
    80),
    (q
    97
    2560), by certificate_kernel⟩

/-- Exact rational interval sin080. -/
def sin080 : IntervalRat :=
  ⟨(q
    46315107847999366463243717387272146318049247
    1235365124003666683927334045614080000000000000),
    (q
    46797786636873573831430647516607625628958753
    1235365124003666683927334045614080000000000000), by certificate_kernel⟩

/-- Exact rational interval cos080. -/
def cos080 : IntervalRat :=
  ⟨(q
    1234478421398829838074065929568622208451133407
    1235365124003666683927334045614080000000000000),
    (q
    1234496611818619712771211970375053167984066593
    1235365124003666683927334045614080000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin080_eq : IntervalRat.sinComputable input080 10 = sin080 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos080_eq : IntervalRat.cosComputable input080 10 = cos080 := by
  certificate_kernel

/-- Exact rational interval input081. -/
def input081 : IntervalRat :=
  ⟨(q
    0
    1),
    (q
    1
    80), by certificate_kernel⟩

/-- Exact rational interval sin081. -/
def sin081 : IntervalRat :=
  ⟨(q
    (-(1 : ℤ))
    34288270112194560000000000000),
    (q
    428603376402432000000000001
    34288270112194560000000000000), by certificate_kernel⟩

/-- Exact rational interval cos081. -/
def cos081 : IntervalRat :=
  ⟨(q
    34285591341092044799999999999
    34288270112194560000000000000),
    (q
    1
    1), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin081_eq : IntervalRat.sinComputable input081 10 = sin081 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos081_eq : IntervalRat.cosComputable input081 10 = cos081 := by
  certificate_kernel

/-- Exact rational interval input082. -/
def input082 : IntervalRat :=
  ⟨(q
    7
    160),
    (q
    3
    64), by certificate_kernel⟩

/-- Exact rational interval sin082. -/
def sin082 : IntervalRat :=
  ⟨(q
    993915424388290844838274213
    22726388698810167590912000000),
    (q
    212991933192652021758831583
    4545277739762033518182400000), by certificate_kernel⟩

/-- Exact rational interval cos082. -/
def cos082 : IntervalRat :=
  ⟨(q
    22701424724703423856615430309
    22726388698810167590912000000),
    (q
    567616070422268827830035266531
    568159717470254189772800000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin082_eq : IntervalRat.sinComputable input082 10 = sin082 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos082_eq : IntervalRat.cosComputable input082 10 = cos082 := by
  certificate_kernel

/-- Exact rational interval input083. -/
def input083 : IntervalRat :=
  ⟨(q
    321
    8192),
    (q
    12841
    327680), by certificate_kernel⟩

/-- Exact rational interval sin083. -/
def sin083 : IntervalRat :=
  ⟨(q
    ((naturalFromChunks [
      73132249154642565055550102979520,
      64211608140524480599738554582490759]) : ℤ)
    (naturalFromChunks [
      1866830993824325939371291095378218,
      43324806170020686069760000000000000])),
    (q
    ((naturalFromChunks [
      73137947728859089862651256946929,
      91137875873981779798435817257509241]) : ℤ)
    (naturalFromChunks [
      1866830993824325939371291095378218,
      43324806170020686069760000000000000])), by certificate_kernel⟩

/-- Exact rational interval cos083. -/
def cos083 : IntervalRat :=
  ⟨(q
    ((naturalFromChunks [
      1865397759306331928574235376160503,
      847983933632998588540996617690759]) : ℤ)
    (naturalFromChunks [
      1866830993824325939371291095378218,
      43324806170020686069760000000000000])),
    (q
    ((naturalFromChunks [
      1865397982554071724224425866993409,
      97602896994137562711663306537509241]) : ℤ)
    (naturalFromChunks [
      1866830993824325939371291095378218,
      43324806170020686069760000000000000])), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin083_eq : IntervalRat.sinComputable input083 10 = sin083 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos083_eq : IntervalRat.cosComputable input083 10 = cos083 := by
  certificate_kernel

/-- Exact rational interval input084. -/
def input084 : IntervalRat :=
  ⟨(q
    12841
    327680),
    (q
    6421
    163840), by certificate_kernel⟩

/-- Exact rational interval sin084. -/
def sin084 : IntervalRat :=
  ⟨(q
    44088747767598900342369920584770977144281262526017256720422659
    1125356260744795247016837321191537925135068058091520000000000000),
    (q
    1190488939960256049341849411576409857935603616223791491818476207
    30384619040109471669454607672171523978646837568471040000000000000), by certificate_kernel⟩

/-- Exact rational interval cos084. -/
def cos084 : IntervalRat :=
  ⟨(q
    4337326860347712858280722215916458619086674535932725204367952359
    4340659862872781667064943953167360568378119652638720000000000000),
    (q
    91083874968919451210177470547533729486387421268683226462826613261
    91153857120328415008363823016514571935940512705413120000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin084_eq : IntervalRat.sinComputable input084 10 = sin084 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos084_eq : IntervalRat.cosComputable input084 10 = cos084 := by
  certificate_kernel

/-- Exact rational interval input085. -/
def input085 : IntervalRat :=
  ⟨(q
    1
    16),
    (q
    3
    40), by certificate_kernel⟩

/-- Exact rational interval sin085. -/
def sin085 : IntervalRat :=
  ⟨(q
    12906347632323217185313
    206695301120000000000000),
    (q
    15492057878264020627187
    206695301120000000000000), by certificate_kernel⟩

/-- Exact rational interval cos085. -/
def cos085 : IntervalRat :=
  ⟨(q
    412228319570641749686251
    413390602240000000000000),
    (q
    1650334308564499799158121
    1653562408960000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin085_eq : IntervalRat.sinComputable input085 10 = sin085 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos085_eq : IntervalRat.cosComputable input085 10 = cos085 := by
  certificate_kernel

/-- Exact rational interval input086. -/
def input086 : IntervalRat :=
  ⟨(q
    23
    640),
    (q
    47
    1280), by certificate_kernel⟩

/-- Exact rational interval sin086. -/
def sin086 : IntervalRat :=
  ⟨(q
    7224277104308498955951450444532113243899
    201068542318305124337131192320000000000000),
    (q
    2460465484311995730544572986421119713367
    67022847439435041445710397440000000000000), by certificate_kernel⟩

/-- Exact rational interval cos086. -/
def cos086 : IntervalRat :=
  ⟨(q
    7441963329845303952802829911879490976417
    7446983048826115716190044160000000000000),
    (q
    602816149506159240942410868018314609214223
    603205626954915373011393576960000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin086_eq : IntervalRat.sinComputable input086 10 = sin086 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos086_eq : IntervalRat.cosComputable input086 10 = cos086 := by
  certificate_kernel

/-- Exact rational interval input087. -/
def input087 : IntervalRat :=
  ⟨(q
    399
    10240),
    (q
    5
    128), by certificate_kernel⟩

/-- Exact rational interval sin087. -/
def sin087 : IntervalRat :=
  ⟨(q
    1503861512218423046882569654081
    38605160125114583872729188925440),
    (q
    471135157447586360571189656077
    12064112539098307460227871539200), by certificate_kernel⟩

/-- Exact rational interval cos087. -/
def cos087 : IntervalRat :=
  ⟨(q
    617211367226596515773065292675977
    617682562001833341963667022807040),
    (q
    19750839057704063271097533186685424149
    19765841984058666942837344729825280000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin087_eq : IntervalRat.sinComputable input087 10 = sin087 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos087_eq : IntervalRat.cosComputable input087 10 = cos087 := by
  certificate_kernel

/-- Exact rational interval input088. -/
def input088 : IntervalRat :=
  ⟨(q
    99
    2560),
    (q
    397
    10240), by certificate_kernel⟩

/-- Exact rational interval sin088. -/
def sin088 : IntervalRat :=
  ⟨(q
    200328006155368709535837889519197071229017875177547
    5181496881069075187063152896855318200320000000000000),
    (q
    200834138161190280136103111091201062396040092950453
    5181496881069075187063152896855318200320000000000000), by certificate_kernel⟩

/-- Exact rational interval cos088. -/
def cos088 : IntervalRat :=
  ⟨(q
    5177603273114064359308644542010371937265350516826187
    5181496881069075187063152896855318200320000000000000),
    (q
    5177622866005053397209231557228291347250488696741813
    5181496881069075187063152896855318200320000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin088_eq : IntervalRat.sinComputable input088 10 = sin088 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos088_eq : IntervalRat.cosComputable input088 10 = cos088 := by
  certificate_kernel

/-- Exact rational interval input089. -/
def input089 : IntervalRat :=
  ⟨(q
    801
    20480),
    (q
    641
    16384), by certificate_kernel⟩

/-- Exact rational interval sin089. -/
def sin089 : IntervalRat :=
  ⟨(q
    22276493659915229474216110765101529587459161186910673423
    569711607002052593802273893853216074599628204408832000000),
    (q
    4456689984207277004087345287134981545627423964716740093
    113942321400410518760454778770643214919925640881766400000), by certificate_kernel⟩

/-- Exact rational interval cos089. -/
def cos089 : IntervalRat :=
  ⟨(q
    569275647758686348512229506521453045576298565995461679631
    569711607002052593802273893853216074599628204408832000000),
    (q
    14231897995009329952653004933974099753692974789373202822281
    14242790175051314845056847346330401864990705110220800000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin089_eq : IntervalRat.sinComputable input089 10 = sin089 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos089_eq : IntervalRat.cosComputable input089 10 = cos089 := by
  certificate_kernel

/-- Exact rational interval input090. -/
def input090 : IntervalRat :=
  ⟨(q
    641
    16384),
    (q
    1603
    40960), by certificate_kernel⟩

/-- Exact rational interval sin090. -/
def sin090 : IntervalRat :=
  ⟨(q
    40478375434846543828196510705945620329363802474426388593
    1034893956869311730161891926090088026136903680000000000000),
    (q
    13497003880584053276862328124503928274326844609217870469
    344964652289770576720630642030029342045634560000000000000), by certificate_kernel⟩

/-- Exact rational interval cos090. -/
def cos090 : IntervalRat :=
  ⟨(q
    344700510964477348260543447172863964083009648625193329531
    344964652289770576720630642030029342045634560000000000000),
    (q
    3102306081652471172577860269006915312270391595093390834221
    3104681870607935190485675778270264078410711040000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin090_eq : IntervalRat.sinComputable input090 10 = sin090 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos090_eq : IntervalRat.cosComputable input090 10 = cos090 := by
  certificate_kernel

/-- Exact rational interval input091. -/
def input091 : IntervalRat :=
  ⟨(q
    3
    80),
    (q
    13
    320), by certificate_kernel⟩

/-- Exact rational interval sin091. -/
def sin091 : IntervalRat :=
  ⟨(q
    5391595224757363554593793756533963
    143815428484658091786240000000000000),
    (q
    5841132558827245236829106877066037
    143815428484658091786240000000000000), by certificate_kernel⟩

/-- Exact rational interval cos091. -/
def cos091 : IntervalRat :=
  ⟨(q
    143696766573764665854387048630113483
    143815428484658091786240000000000000),
    (q
    143714322168175287548244017349749557
    143815428484658091786240000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin091_eq : IntervalRat.sinComputable input091 10 = sin091 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos091_eq : IntervalRat.cosComputable input091 10 = cos091 := by
  certificate_kernel

/-- Exact rational interval input092. -/
def input092 : IntervalRat :=
  ⟨(q
    1601
    40960),
    (q
    801
    20480), by certificate_kernel⟩

/-- Exact rational interval sin092. -/
def sin092 : IntervalRat :=
  ⟨(q
    5119420812631176939929839645176637463755398850352879
    131008711264561308433399223861230761410560000000000000),
    (q
    5122620082493240637461146792612622366616909633743121
    131008711264561308433399223861230761410560000000000000), by certificate_kernel⟩

/-- Exact rational interval cos092. -/
def cos092 : IntervalRat :=
  ⟨(q
    130908522271166175634637772308389863473710653399945199
    131008711264561308433399223861230761410560000000000000),
    (q
    130908647327941061434076306073008449326623043391973201
    131008711264561308433399223861230761410560000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin092_eq : IntervalRat.sinComputable input092 10 = sin092 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos092_eq : IntervalRat.cosComputable input092 10 = cos092 := by
  certificate_kernel

/-- Exact rational interval input093. -/
def input093 : IntervalRat :=
  ⟨(q
    397
    10240),
    (q
    199
    5120), by certificate_kernel⟩

/-- Exact rational interval sin093. -/
def sin093 : IntervalRat :=
  ⟨(q
    32687765487614522192584714005509451799331527267
    843342591319836456227726708472545280000000000000),
    (q
    1213709031397176866485479103816298473325427879
    31234910789623572452878766980464640000000000000), by certificate_kernel⟩

/-- Exact rational interval cos093. -/
def cos093 : IntervalRat :=
  ⟨(q
    2528117009630215447843272049886226765864282040681
    2530027773959509368683180125417635840000000000000),
    (q
    842708866866581508102147157016078230751667170893
    843342591319836456227726708472545280000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin093_eq : IntervalRat.sinComputable input093 10 = sin093 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos093_eq : IntervalRat.cosComputable input093 10 = cos093 := by
  certificate_kernel

/-- Exact rational interval input094. -/
def input094 : IntervalRat :=
  ⟨(q
    799
    20480),
    (q
    5
    128), by certificate_kernel⟩

/-- Exact rational interval sin094. -/
def sin094 : IntervalRat :=
  ⟨(q
    80306456028117492045383655445831
    2058941873339444473212223409356800),
    (q
    837573081629695472362891318363
    21447311180619213262627327180800), by certificate_kernel⟩

/-- Exact rational interval cos094. -/
def cos094 : IntervalRat :=
  ⟨(q
    3291793959339284049884026829895619
    3294306997343111157139557454970880),
    (q
    180578755957256340526516712622400466147
    180716269568536383477370008958402560000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin094_eq : IntervalRat.sinComputable input094 10 = sin094 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos094_eq : IntervalRat.cosComputable input094 10 = cos094 := by
  certificate_kernel

/-- Exact rational interval input095. -/
def input095 : IntervalRat :=
  ⟨(q
    3207
    81920),
    (q
    1283
    32768), by certificate_kernel⟩

/-- Exact rational interval sin095. -/
def sin095 : IntervalRat :=
  ⟨(q
    45664958303846825109429214972049224498109002540490859133237
    1166769371140203712107056934611386520780038562629287936000000),
    (q
    1304916614810110885665891475518646245905564436008391030073
    33336267746862963203058769560325329165143958932265369600000), by certificate_kernel⟩

/-- Exact rational interval cos095. -/
def cos095 : IntervalRat :=
  ⟨(q
    1165875133386933019398881705246712875373856232195559525628213
    1166769371140203712107056934611386520780038562629287936000000),
    (q
    29146885304917021630187109561033814432101305317932363253279187
    29169234278505092802676423365284663019500964065732198400000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin095_eq : IntervalRat.sinComputable input095 10 = sin095 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos095_eq : IntervalRat.cosComputable input095 10 = cos095 := by
  certificate_kernel

/-- Exact rational interval input096. -/
def input096 : IntervalRat :=
  ⟨(q
    197
    5120),
    (q
    99
    2560), by certificate_kernel⟩

/-- Exact rational interval sin096. -/
def sin096 : IntervalRat :=
  ⟨(q
    53334182569428677984744864245574288206111
    1386492843999625907887019130880000000000000),
    (q
    53605049114497447348405034300221592753889
    1386492843999625907887019130880000000000000), by certificate_kernel⟩

/-- Exact rational interval cos096. -/
def cos096 : IntervalRat :=
  ⟨(q
    1385456212227468257863173698106574494061951
    1386492843999625907887019130880000000000000),
    (q
    1385466658102192608442300680935385164977529
    1386492843999625907887019130880000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin096_eq : IntervalRat.sinComputable input096 10 = sin096 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos096_eq : IntervalRat.cosComputable input096 10 = cos096 := by
  certificate_kernel

/-- Exact rational interval input097. -/
def input097 : IntervalRat :=
  ⟨(q
    1
    80),
    (q
    1
    40), by certificate_kernel⟩

/-- Exact rational interval sin097. -/
def sin097 : IntervalRat :=
  ⟨(q
    7750266394787746133537
    620085903360000000000000),
    (q
    139515695053700697603667
    5580773130240000000000000), by certificate_kernel⟩

/-- Exact rational interval cos097. -/
def cos097 : IntervalRat :=
  ⟨(q
    11158058322689101826639981
    11161546260480000000000000),
    (q
    133928091721135337503679953
    133938555125760000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin097_eq : IntervalRat.sinComputable input097 10 = sin097 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos097_eq : IntervalRat.cosComputable input097 10 = cos097 := by
  certificate_kernel

/-- Exact rational interval input098. -/
def input098 : IntervalRat :=
  ⟨(q
    6419
    163840),
    (q
    12839
    327680), by certificate_kernel⟩

/-- Exact rational interval sin098. -/
def sin098 : IntervalRat :=
  ⟨(q
    ((naturalFromChunks [
      8124540407606158110866551340793,
      74536615566072261390159475591126529]) : ℤ)
    (naturalFromChunks [
      207425665980480659930143455042024,
      27036089574446742896640000000000000])),
    (q
    ((naturalFromChunks [
      8125173582468634973205381349153,
      14929325263354211528683908020265471]) : ℤ)
    (naturalFromChunks [
      207425665980480659930143455042024,
      27036089574446742896640000000000000])), by certificate_kernel⟩

/-- Exact rational interval cos098. -/
def cos098 : IntervalRat :=
  ⟨(q
    ((naturalFromChunks [
      621799401890062825676667167327552,
      19144258473801377116786729817332227]) : ℤ)
    (naturalFromChunks [
      622276997941441979790430365126072,
      81108268723340228689920000000000000])),
    (q
    ((naturalFromChunks [
      1865398428883155834590981868920704,
      16417759353230822573257282588144119]) : ℤ)
    (naturalFromChunks [
      1866830993824325939371291095378218,
      43324806170020686069760000000000000])), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin098_eq : IntervalRat.sinComputable input098 10 = sin098 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos098_eq : IntervalRat.cosComputable input098 10 = cos098 := by
  certificate_kernel

/-- Exact rational interval input099. -/
def input099 : IntervalRat :=
  ⟨(q
    12839
    327680),
    (q
    321
    8192), by certificate_kernel⟩

/-- Exact rational interval sin099. -/
def sin099 : IntervalRat :=
  ⟨(q
    134527235141303682368171185128765279741827709772319
    3434314760573715963796500613987847671920984064000000),
    (q
    26907543704053109523376832084765027587268151052589
    686862952114743192759300122797569534384196812800000), by certificate_kernel⟩

/-- Exact rational interval cos099. -/
def cos099 : IntervalRat :=
  ⟨(q
    3431678521958667995717470426040351459056346620614313
    3434314760573715963796500613987847671920984064000000),
    (q
    2745343146099426446411525522307964867747818973237383829
    2747451808458972771037200491190278137536787251200000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin099_eq : IntervalRat.sinComputable input099 10 = sin099 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos099_eq : IntervalRat.cosComputable input099 10 = cos099 := by
  certificate_kernel

/-- Exact rational interval input100. -/
def input100 : IntervalRat :=
  ⟨(q
    97
    2560),
    (q
    49
    1280), by certificate_kernel⟩

/-- Exact rational interval sin100. -/
def sin100 : IntervalRat :=
  ⟨(q
    1088107440281577805623514123442939449331
    28724077474043589191018741760000000000000),
    (q
    366443498586794836166493814526865730223
    9574692491347863063672913920000000000000), by certificate_kernel⟩

/-- Exact rational interval cos100. -/
def cos100 : IntervalRat :=
  ⟨(q
    86109099250298692546989792625091248586953
    86172232422130767573056225280000000000000),
    (q
    9567820140236202187571854014793557773963
    9574692491347863063672913920000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin100_eq : IntervalRat.sinComputable input100 10 = sin100 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos100_eq : IntervalRat.cosComputable input100 10 = cos100 := by
  certificate_kernel

/-- Exact rational interval input101. -/
def input101 : IntervalRat :=
  ⟨(q
    1603
    40960),
    (q
    3207
    81920), by certificate_kernel⟩

/-- Exact rational interval sin101. -/
def sin101 : IntervalRat :=
  ⟨(q
    21499220666215007456953295423008108253317499412783248476697
    549490361691794554207440098238055627507357450240000000000000),
    (q
    21505930025142540646747603449059445066868103272679656355303
    549490361691794554207440098238055627507357450240000000000000), by certificate_kernel⟩

/-- Exact rational interval cos101. -/
def cos101 : IntervalRat :=
  ⟨(q
    549069351426998032039164682724821926579865361550245129390617
    549490361691794554207440098238055627507357450240000000000000),
    (q
    549069613976645162557219745514697715804962422471374200862183
    549490361691794554207440098238055627507357450240000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin101_eq : IntervalRat.sinComputable input101 10 = sin101 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos101_eq : IntervalRat.cosComputable input101 10 = cos101 := by
  certificate_kernel

/-- Exact rational interval input102. -/
def input102 : IntervalRat :=
  ⟨(q
    47
    1280),
    (q
    3
    80), by certificate_kernel⟩

/-- Exact rational interval sin102. -/
def sin102 : IntervalRat :=
  ⟨(q
    31825600276727018480388105649
    866942928268820480000000000000),
    (q
    2031440930312822113741764061
    54183933016801280000000000000), by certificate_kernel⟩

/-- Exact rational interval cos102. -/
def cos102 : IntervalRat :=
  ⟨(q
    1732666855015318342257421679953
    1733885856537640960000000000000),
    (q
    443575583568080760988205872872617
    443874779273636085760000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin102_eq : IntervalRat.sinComputable input102 10 = sin102 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos102_eq : IntervalRat.cosComputable input102 10 = cos102 := by
  certificate_kernel

/-- Exact rational interval input103. -/
def input103 : IntervalRat :=
  ⟨(q
    1
    32),
    (q
    3
    80), by certificate_kernel⟩

/-- Exact rational interval sin103. -/
def sin103 : IntervalRat :=
  ⟨(q
    13225398993546291268747813
    423311976693760000000000000),
    (q
    15871615616413568082502187
    423311976693760000000000000), by certificate_kernel⟩

/-- Exact rational interval cos103. -/
def cos103 : IntervalRat :=
  ⟨(q
    211507179840558704299844219
    211655988346880000000000000),
    (q
    1692421222455828559199149373
    1693247906775040000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin103_eq : IntervalRat.sinComputable input103 10 = sin103 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos103_eq : IntervalRat.cosComputable input103 10 = cos103 := by
  certificate_kernel

/-- Exact rational interval input104. -/
def input104 : IntervalRat :=
  ⟨(q
    1283
    32768),
    (q
    401
    10240), by certificate_kernel⟩

/-- Exact rational interval sin104. -/
def sin104 : IntervalRat :=
  ⟨(q
    67608251205822231167762278470333128743613994773533
    1727165627023025062354384298951772733440000000000000),
    (q
    2504399840086501687947308784681635971784961466721
    63969097297149076383495714775991582720000000000000), by certificate_kernel⟩

/-- Exact rational interval cos104. -/
def cos104 : IntervalRat :=
  ⟨(q
    165680781748983361024783962894316982925594246580974793
    165807900194210405986020892699370182410240000000000000),
    (q
    673242702735881691572150620813669103525616330270542359
    673759086503458157657481722714901058682880000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin104_eq : IntervalRat.sinComputable input104 10 = sin104 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos104_eq : IntervalRat.cosComputable input104 10 = cos104 := by
  certificate_kernel

/-- Exact rational interval input105. -/
def input105 : IntervalRat :=
  ⟨(q
    3
    40),
    (q
    1
    10), by certificate_kernel⟩

/-- Exact rational interval sin105. -/
def sin105 : IntervalRat :=
  ⟨(q
    38256279078283533997
    510935040000000000000),
    (q
    12761406946718211407
    127733760000000000000), by certificate_kernel⟩

/-- Exact rational interval cos105. -/
def cos105 : IntervalRat :=
  ⟨(q
    508381561904872090417
    510935040000000000000),
    (q
    1164569674238875640279
    1167851520000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin105_eq : IntervalRat.sinComputable input105 10 = sin105 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos105_eq : IntervalRat.cosComputable input105 10 = cos105 := by
  certificate_kernel

/-- Exact rational interval input106. -/
def input106 : IntervalRat :=
  ⟨(q
    6421
    163840),
    (q
    12843
    327680), by certificate_kernel⟩

/-- Exact rational interval sin106. -/
def sin106 : IntervalRat :=
  ⟨(q
    90300783503833551848939103492560171836900171306922492237716737853
    (naturalFromChunks [
      23047296220053406658904828338002,
      69670676619382971432960000000000000])),
    (q
    90307818781204945219864426646591996965247422598429709169320702147
    (naturalFromChunks [
      23047296220053406658904828338002,
      69670676619382971432960000000000000])), by certificate_kernel⟩

/-- Exact rational interval cos106. -/
def cos106 : IntervalRat :=
  ⟨(q
    ((naturalFromChunks [
      23029596455222023385243757666095,
      68979040680914929787038959468105533]) : ℤ)
    (naturalFromChunks [
      23047296220053406658904828338002,
      69670676619382971432960000000000000])),
    (q
    ((naturalFromChunks [
      23029599211796248493146351399608,
      36574690647598908956214451474706627]) : ℤ)
    (naturalFromChunks [
      23047296220053406658904828338002,
      69670676619382971432960000000000000])), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin106_eq : IntervalRat.sinComputable input106 10 = sin106 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos106_eq : IntervalRat.cosComputable input106 10 = cos106 := by
  certificate_kernel

/-- Exact rational interval input107. -/
def input107 : IntervalRat :=
  ⟨(q
    12843
    327680),
    (q
    3211
    81920), by certificate_kernel⟩

/-- Exact rational interval sin107. -/
def sin107 : IntervalRat :=
  ⟨(q
    1744015869589201250811407667340490327954671582638462470822189
    44508719297035358890802647957282505828095953469440000000000000),
    (q
    1744151734202209918843412897904172773471822548527146661209811
    44508719297035358890802647957282505828095953469440000000000000), by certificate_kernel⟩

/-- Exact rational interval cos107. -/
def cos107 : IntervalRat :=
  ⟨(q
    44474532356983436942081848375664565699768717902938197104431469
    44508719297035358890802647957282505828095953469440000000000000),
    (q
    44474537680867887205709283367253116788945810805671641203903831
    44508719297035358890802647957282505828095953469440000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin107_eq : IntervalRat.sinComputable input107 10 = sin107 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos107_eq : IntervalRat.cosComputable input107 10 = cos107 := by
  certificate_kernel

/-- Exact rational interval input108. -/
def input108 : IntervalRat :=
  ⟨(q
    1
    32),
    (q
    21
    640), by certificate_kernel⟩

/-- Exact rational interval sin108. -/
def sin108 : IntervalRat :=
  ⟨(q
    16230221998854600298711651026630437
    519460313115660973506560000000000000),
    (q
    17042017456078158416074468653369563
    519460313115660973506560000000000000), by certificate_kernel⟩

/-- Exact rational interval cos108. -/
def cos108 : IntervalRat :=
  ⟨(q
    519180694761153736526462369183430437
    519460313115660973506560000000000000),
    (q
    519206693141158552511607688493369563
    519460313115660973506560000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin108_eq : IntervalRat.sinComputable input108 10 = sin108 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos108_eq : IntervalRat.cosComputable input108 10 = cos108 := by
  certificate_kernel

/-- Exact rational interval input109. -/
def input109 : IntervalRat :=
  ⟨(q
    199
    5120),
    (q
    797
    20480), by certificate_kernel⟩

/-- Exact rational interval sin109. -/
def sin109 : IntervalRat :=
  ⟨(q
    137447684688966120492495619570546890033312894133536649
    3537235204143155327701779044253230558085120000000000000),
    (q
    137620444795542478411013269970350834136848991148767351
    3537235204143155327701779044253230558085120000000000000), by certificate_kernel⟩

/-- Exact rational interval cos109. -/
def cos109 : IntervalRat :=
  ⟨(q
    3534557047296445979321568732012693416620809152351766409
    3537235204143155327701779044253230558085120000000000000),
    (q
    10603691293560685590776511322163579058973134966134204773
    10611705612429465983105337132759691674255360000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin109_eq : IntervalRat.sinComputable input109 10 = sin109 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos109_eq : IntervalRat.cosComputable input109 10 = cos109 := by
  certificate_kernel

/-- Exact rational interval input110. -/
def input110 : IntervalRat :=
  ⟨(q
    797
    20480),
    (q
    399
    10240), by certificate_kernel⟩

/-- Exact rational interval sin110. -/
def sin110 : IntervalRat :=
  ⟨(q
    355541786612374525513582782773855915539567899703
    9138442471021296626213673539427368960000000000000),
    (q
    355988112401869429823031153507130009713470180297
    9138442471021296626213673539427368960000000000000), by certificate_kernel⟩

/-- Exact rational interval cos110. -/
def cos110 : IntervalRat :=
  ⟨(q
    9131506085006681481718550095077228696543473580983
    9138442471021296626213673539427368960000000000000),
    (q
    9131523460733183870898304567356057296531414827177
    9138442471021296626213673539427368960000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin110_eq : IntervalRat.sinComputable input110 10 = sin110 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos110_eq : IntervalRat.cosComputable input110 10 = cos110 := by
  certificate_kernel

/-- Exact rational interval input111. -/
def input111 : IntervalRat :=
  ⟨(q
    3207
    81920),
    (q
    401
    10240), by certificate_kernel⟩

/-- Exact rational interval sin111. -/
def sin111 : IntervalRat :=
  ⟨(q
    28970448050205641441498139535570849071732093265657
    740213840152725026723307556693616885760000000000000),
    (q
    28979486172571335719747438666359227000677116174343
    740213840152725026723307556693616885760000000000000), by certificate_kernel⟩

/-- Exact rational interval cos111. -/
def cos111 : IntervalRat :=
  ⟨(q
    10355048858995018476803198922907094867185263399375143
    10362993762138150374126305793710636400640000000000000),
    (q
    662723443970374071313027672401554248438898857108468633
    663231600776841623944083570797480729640960000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin111_eq : IntervalRat.sinComputable input111 10 = sin111 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos111_eq : IntervalRat.cosComputable input111 10 = cos111 := by
  certificate_kernel

/-- Exact rational interval input112. -/
def input112 : IntervalRat :=
  ⟨(q
    1
    40),
    (q
    9
    320), by certificate_kernel⟩

/-- Exact rational interval sin112. -/
def sin112 : IntervalRat :=
  ⟨(q
    44381626245465123865086269091511
    1775499117094544343040000000000000),
    (q
    49930711216441005979233282396489
    1775499117094544343040000000000000), by certificate_kernel⟩

/-- Exact rational interval cos112. -/
def cos112 : IntervalRat :=
  ⟨(q
    1774796929895837037957983152926391
    1775499117094544343040000000000000),
    (q
    253563472884835019068351497891887
    253642731013506334720000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin112_eq : IntervalRat.sinComputable input112 10 = sin112 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos112_eq : IntervalRat.cosComputable input112 10 = cos112 := by
  certificate_kernel

/-- Exact rational interval input113. -/
def input113 : IntervalRat :=
  ⟨(q
    21
    640),
    (q
    11
    320), by certificate_kernel⟩

/-- Exact rational interval sin113. -/
def sin113 : IntervalRat :=
  ⟨(q
    428910404355271078837101471887399
    13074129862241644707840000000000000),
    (q
    449342572767860674534340096208601
    13074129862241644707840000000000000), by certificate_kernel⟩

/-- Exact rational interval cos113. -/
def cos113 : IntervalRat :=
  ⟨(q
    13066406093775131751712333058198579
    13074129862241644707840000000000000),
    (q
    3266773089479568807927459776814199
    3268532465560411176960000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin113_eq : IntervalRat.sinComputable input113 10 = sin113 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos113_eq : IntervalRat.cosComputable input113 10 = cos113 := by
  certificate_kernel

/-- Exact rational interval input114. -/
def input114 : IntervalRat :=
  ⟨(q
    401
    10240),
    (q
    6417
    163840), by certificate_kernel⟩

/-- Exact rational interval sin114. -/
def sin114 : IntervalRat :=
  ⟨(q
    44057860894835211005055515748718800945925486042038237206242207
    1125356260744795247016837321191537925135068058091520000000000000),
    (q
    44064731280292277455204511774844718321751153155371891353885793
    1125356260744795247016837321191537925135068058091520000000000000), by certificate_kernel⟩

/-- Exact rational interval cos114. -/
def cos114 : IntervalRat :=
  ⟨(q
    1124493225096019784653246013495120693933661876840121179264082847
    1125356260744795247016837321191537925135068058091520000000000000),
    (q
    1124493494093588207708897103024158734967634656129088622419680353
    1125356260744795247016837321191537925135068058091520000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin114_eq : IntervalRat.sinComputable input114 10 = sin114 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos114_eq : IntervalRat.cosComputable input114 10 = cos114 := by
  certificate_kernel

/-- Exact rational interval input115. -/
def input115 : IntervalRat :=
  ⟨(q
    799
    20480),
    (q
    1599
    40960), by certificate_kernel⟩

/-- Exact rational interval sin115. -/
def sin115 : IntervalRat :=
  ⟨(q
    10464937511557683447554690825374630276128625511772532721
    268305840669821559671601610467800599368826880000000000000),
    (q
    10471489609987254475651414253664454016070977982942859279
    268305840669821559671601610467800599368826880000000000000), by certificate_kernel⟩

/-- Exact rational interval cos115. -/
def cos115 : IntervalRat :=
  ⟨(q
    268101421285196564628556889783154368729092559889162776561
    268305840669821559671601610467800599368826880000000000000),
    (q
    268101676921703285502615359339476737693447974163091738639
    268305840669821559671601610467800599368826880000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin115_eq : IntervalRat.sinComputable input115 10 = sin115 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos115_eq : IntervalRat.cosComputable input115 10 = cos115 := by
  certificate_kernel

/-- Exact rational interval input116. -/
def input116 : IntervalRat :=
  ⟨(q
    1599
    40960),
    (q
    5
    128), by certificate_kernel⟩

/-- Exact rational interval sin116. -/
def sin116 : IntervalRat :=
  ⟨(q
    1542848839354056347036542240528369
    39531683968117333885674689459650560),
    (q
    120610485442772053221531987345427
    3088412810009166709818335114035200), by certificate_kernel⟩

/-- Exact rational interval cos116. -/
def cos116 : IntervalRat :=
  ⟨(q
    22572301438206010512436190529025711
    22589533696067047934671251119800320),
    (q
    80899205540722865406812088912038731205749
    80960888766704299797861764013364346880000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin116_eq : IntervalRat.sinComputable input116 10 = sin116 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos116_eq : IntervalRat.cosComputable input116 10 = cos116 := by
  certificate_kernel

/-- Exact rational interval input117. -/
def input117 : IntervalRat :=
  ⟨(q
    47
    1280),
    (q
    19
    512), by certificate_kernel⟩

/-- Exact rational interval sin117. -/
def sin117 : IntervalRat :=
  ⟨(q
    193496118125386163724083536181594784599
    5270891195748977851423291927953408000000),
    (q
    39111105523933561167915022950645137237
    1054178239149795570284658385590681600000), by certificate_kernel⟩

/-- Exact rational interval cos117. -/
def cos117 : IntervalRat :=
  ⟨(q
    15801786948935920416886267975488611691013
    15812673587246933554269875783860224000000),
    (q
    18811922572219149224942458207551716867383
    18824611413389206612226042599833600000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin117_eq : IntervalRat.sinComputable input117 10 = sin117 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos117_eq : IntervalRat.cosComputable input117 10 = cos117 := by
  certificate_kernel

/-- Exact rational interval input118. -/
def input118 : IntervalRat :=
  ⟨(q
    19
    512),
    (q
    3
    80), by certificate_kernel⟩

/-- Exact rational interval sin118. -/
def sin118 : IntervalRat :=
  ⟨(q
    1029253456105894848092144563393
    27742173704602255360000000000000),
    (q
    32502898634343941259988307101
    866942928268820480000000000000), by certificate_kernel⟩

/-- Exact rational interval cos118. -/
def cos118 : IntervalRat :=
  ⟨(q
    27722669727121390447656138613393
    27742173704602255360000000000000),
    (q
    28388427765822779031384535913101193
    28407985873512709488640000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin118_eq : IntervalRat.sinComputable input118 10 = sin118 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos118_eq : IntervalRat.cosComputable input118 10 = cos118 := by
  certificate_kernel

/-- Exact rational interval input119. -/
def input119 : IntervalRat :=
  ⟨(q
    803
    20480),
    (q
    1285
    32768), by certificate_kernel⟩

/-- Exact rational interval sin119. -/
def sin119 : IntervalRat :=
  ⟨(q
    24392596050849521089839213000925298081322627034110589793
    622276997941441979790430365126072811082687233402286899200),
    (q
    8132131700538239969681509063749369027715810450912717877
    207425665980480659930143455042024270360895744467428966400), by certificate_kernel⟩

/-- Exact rational interval cos119. -/
def cos119 : IntervalRat :=
  ⟨(q
    373079149956078915494092354783387976680949568909444073991
    373366198764865187874258219075643686649612340041372139520),
    (q
    1727218700529111011615656358257609636276273482876039600911
    1728547216504005499417862125350202253007464537228574720000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin119_eq : IntervalRat.sinComputable input119 10 = sin119 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos119_eq : IntervalRat.cosComputable input119 10 = cos119 := by
  certificate_kernel

/-- Exact rational interval input120. -/
def input120 : IntervalRat :=
  ⟨(q
    1285
    32768),
    (q
    3213
    81920), by certificate_kernel⟩

/-- Exact rational interval sin120. -/
def sin120 : IntervalRat :=
  ⟨(q
    3077541231234443727140837486233575248660451792996827042189
    78498623098827793458205728319722232501051064320000000000000),
    (q
    3078020471635306619044480696689166340420774651803172957811
    78498623098827793458205728319722232501051064320000000000000), by certificate_kernel⟩

/-- Exact rational interval cos120. -/
def cos120 : IntervalRat :=
  ⟨(q
    78438253547120207578164056062466577507978218420762827042189
    78498623098827793458205728319722232501051064320000000000000),
    (q
    78438272337220202267035908606828116917088038831540672957811
    78498623098827793458205728319722232501051064320000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin120_eq : IntervalRat.sinComputable input120 10 = sin120 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos120_eq : IntervalRat.cosComputable input120 10 = cos120 := by
  certificate_kernel

/-- Exact rational interval input121. -/
def input121 : IntervalRat :=
  ⟨(q
    1603
    40960),
    (q
    6413
    163840), by certificate_kernel⟩

/-- Exact rational interval sin121. -/
def sin121 : IntervalRat :=
  ⟨(q
    108074636423113604969252693127945175130398156793090542383996011
    2762238094555406515404964333833774907149712506224640000000000000),
    (q
    108091500091135809439970185752736105406757257098839218998403989
    2762238094555406515404964333833774907149712506224640000000000000), by certificate_kernel⟩

/-- Exact rational interval cos121. -/
def cos121 : IntervalRat :=
  ⟨(q
    8280367122305282474081451925363468069207333257581179986545431873
    8286714283666219546214893001501324721449137518673920000000000000),
    (q
    2760123033956914116826024151446462758127501634161251840477029269
    2762238094555406515404964333833774907149712506224640000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin121_eq : IntervalRat.sinComputable input121 10 = sin121 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos121_eq : IntervalRat.cosComputable input121 10 = cos121 := by
  certificate_kernel

/-- Exact rational interval input122. -/
def input122 : IntervalRat :=
  ⟨(q
    6413
    163840),
    (q
    3207
    81920), by certificate_kernel⟩

/-- Exact rational interval sin122. -/
def sin122 : IntervalRat :=
  ⟨(q
    21502573632763303576934395102786564147336941014937711708697
    549490361691794554207440098238055627507357450240000000000000),
    (q
    21505928312360651115675905404289895151418315706471861155303
    549490361691794554207440098238055627507357450240000000000000), by certificate_kernel⟩

/-- Exact rational interval cos122. -/
def cos122 : IntervalRat :=
  ⟨(q
    549069351443761434805273606469178220378378272876749345582617
    549490361691794554207440098238055627507357450240000000000000),
    (q
    78438497532688579423658173590936974614315805880107471899169
    78498623098827793458205728319722232501051064320000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin122_eq : IntervalRat.sinComputable input122 10 = sin122 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos122_eq : IntervalRat.cosComputable input122 10 = cos122 := by
  certificate_kernel

/-- Exact rational interval input123. -/
def input123 : IntervalRat :=
  ⟨(q
    6417
    163840),
    (q
    3209
    81920), by certificate_kernel⟩

/-- Exact rational interval sin123. -/
def sin123 : IntervalRat :=
  ⟨(q
    1742794269911638302265522588079174397724561037067584354969191
    44508719297035358890802647957282505828095953469440000000000000),
    (q
    1743065999045604157146304610884598658746284332391530939750809
    44508719297035358890802647957282505828095953469440000000000000), by certificate_kernel⟩

/-- Exact rational interval cos123. -/
def cos123 : IntervalRat :=
  ⟨(q
    44474574924877743824439622111887206291474228361562275200813671
    44508719297035358890802647957282505828095953469440000000000000),
    (q
    44474585565599808362753486623916333590511391125901641361384089
    44508719297035358890802647957282505828095953469440000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin123_eq : IntervalRat.sinComputable input123 10 = sin123 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos123_eq : IntervalRat.cosComputable input123 10 = cos123 := by
  certificate_kernel

/-- Exact rational interval input124. -/
def input124 : IntervalRat :=
  ⟨(q
    97
    2560),
    (q
    39
    1024), by certificate_kernel⟩

/-- Exact rational interval sin124. -/
def sin124 : IntervalRat :=
  ⟨(q
    15145269644066596029213517288335169064233
    399806858107181727396848217349947392000000),
    (q
    3044675140737422942138708746864712108587
    79961371621436345479369643469989478400000), by certificate_kernel⟩

/-- Exact rational interval cos124. -/
def cos124 : IntervalRat :=
  ⟨(q
    399516925150541993283511566213436901018921
    399806858107181727396848217349947392000000),
    (q
    9987997288799972265020197201133144042845951
    9995171452679543184921205433748684800000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin124_eq : IntervalRat.sinComputable input124 10 = sin124 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos124_eq : IntervalRat.cosComputable input124 10 = cos124 := by
  certificate_kernel

/-- Exact rational interval input125. -/
def input125 : IntervalRat :=
  ⟨(q
    39
    1024),
    (q
    49
    1280), by certificate_kernel⟩

/-- Exact rational interval sin125. -/
def sin125 : IntervalRat :=
  ⟨(q
    3281148725155154700174281759794066715993
    86172232422130767573056225280000000000000),
    (q
    3297983329349498220924392139550363284007
    86172232422130767573056225280000000000000), by certificate_kernel⟩

/-- Exact rational interval cos125. -/
def cos125 : IntervalRat :=
  ⟨(q
    10763637416046819335210264725710950803171
    10771529052766345946632028160000000000000),
    (q
    1377755871646289018325519123546809369028487
    1378755718754092281168899604480000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin125_eq : IntervalRat.sinComputable input125 10 = sin125 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos125_eq : IntervalRat.cosComputable input125 10 = cos125 := by
  certificate_kernel

/-- Exact rational interval input126. -/
def input126 : IntervalRat :=
  ⟨(q
    6417
    163840),
    (q
    2567
    65536), by certificate_kernel⟩

/-- Exact rational interval sin126. -/
def sin126 : IntervalRat :=
  ⟨(q
    93565558640523833734553653708034888438930591462784819631818073
    2389543672095137202395252602084119594557518976264781692928000000),
    (q
    18714570562755400475114382011110790505215657178255565868747707
    477908734419027440479050520416823918911503795252956338585600000), by certificate_kernel⟩

/-- Exact rational interval cos126. -/
def cos126 : IntervalRat :=
  ⟨(q
    341101549383209517657991590756653059456033655715564425561814943
    341363381727876743199321800297731370651074139466397384704000000),
    (q
    59692778282651184994458519628597260497990412485753390425609239119
    59738591802378430059881315052102989863937974406619542323200000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin126_eq : IntervalRat.sinComputable input126 10 = sin126 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos126_eq : IntervalRat.cosComputable input126 10 = cos126 := by
  certificate_kernel

/-- Exact rational interval input127. -/
def input127 : IntervalRat :=
  ⟨(q
    2567
    65536),
    (q
    3209
    81920), by certificate_kernel⟩

/-- Exact rational interval sin127. -/
def sin127 : IntervalRat :=
  ⟨(q
    193658896112619886811291066451785477838909491421657564802799
    4945413255226150987866960884142500647566217052160000000000000),
    (q
    581021976527756203454924273265169738379762019135173225591603
    14836239765678452963600882652427501942698651156480000000000000), by certificate_kernel⟩

/-- Exact rational interval cos127. -/
def cos127 : IntervalRat :=
  ⟨(q
    14824858308519337393864211843988190998715830068079991643008397
    14836239765678452963600882652427501942698651156480000000000000),
    (q
    44474580246126304332769439280625891433796640789307406948337309
    44508719297035358890802647957282505828095953469440000000000000), by certificate_kernel⟩

/-- The cached sin interval agrees with the original evaluator. -/
theorem sin127_eq : IntervalRat.sinComputable input127 10 = sin127 := by
  certificate_kernel

/-- The cached cos interval agrees with the original evaluator. -/
theorem cos127_eq : IntervalRat.cosComputable input127 10 = cos127 := by
  certificate_kernel

end GerverSofa.PartE.CertificateCache
