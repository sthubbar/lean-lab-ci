/-
Certified evaluation of the bounds τ_n of BJS display 31, Bordignon, Johnston and
Starichkova, arXiv 2207.09452v6, papers/P0009.pdf, Lemma 11 and Proposition 13, pages 11 to
14, with c_n of Table 2, at ε = 1/100000, for 1 ≤ n ≤ 500. It proves the LEAFs
tau_odd_le500_1122c and tau_even_le500_1122c of Split1122cTauSum.lean and
tau500_value1122c of Split1122cTauTail.lean.
Method: an integer table tauTab1122e of upper bounds for 10 ^ 30 τ_n, rounded up at each
step and produced by notes/burst-20261124/Cai2002-S9-14-scripts/tau.py, is checked step by
step by decide +kernel against an integer upper bound of the recursion, stepNat1122e, whose
soundness for the real recursion is proved here. The constants γ = e ^ 0.2, e ^ 0.4,
e ^ 0.6, e ^ 0.8 and 4 e / 3 are replaced by 12 digit decimal upper bounds, proved from
Real.exp_bound and Real.exp_one_lt_d9. No native_decide.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Split1122cTwinT

open Finset Real
noncomputable section
namespace LeanLab.Cai2002

/-! ### Integer side -/

/-- The scale 10 ^ 30 of the integer table. -/
def tauS1122e : ℕ := 10 ^ 30

/-- Ceiling division. -/
def cdiv1122e (a b : ℕ) : ℕ := (a + b - 1) / b

/-- 100 c_n of BJS Table 2, page 7, for 1 ≤ n ≤ 500; same case split as bjsC306. -/
def aN1122e (n : ℕ) : ℕ :=
  if n ≤ 1 then 100 else if n = 2 then 33 else if n = 3 then 39 else if n = 4 then 45
  else if n = 5 then 51 else if n = 6 then 54 else if n = 7 then 57
  else if n = 8 then 58 else if n ≤ 10 then 61 else if n ≤ 12 then 63
  else if n = 13 then 64 else if n = 14 then 65 else if n ≤ 18 then 66
  else if n ≤ 20 then 67 else if n ≤ 26 then 68 else if n ≤ 34 then 69
  else if n ≤ 46 then 70 else if n ≤ 82 then 71 else if n ≤ 345 then 72
  else 73

/-- Upper bound for 10 ^ 30 c_n ^ k. -/
def cpow1122e (n k : ℕ) : ℕ := cdiv1122e (aN1122e n ^ k * tauS1122e) (100 ^ k)

/-- Integer upper bound for 10 ^ 30 t ξ, with κ = k / 10000, γ ≤ g / 10 ^ 30,
t ≤ T / 10 ^ 30, cp ≤ CP / 10 ^ 30, cc ≤ CC / 10 ^ 30, ε = 1/100000. -/
def brNat1122e (k g T CP CC : ℕ) : ℕ :=
  cdiv1122e (k * T * tauS1122e * 10 ^ 5 + (g * 10 ^ 4 + k * tauS1122e) * T +
    2 * g * CP * 10 ^ 9 + 2 * CC * tauS1122e * 10 ^ 9) (tauS1122e * 10 ^ 9)

/-- Integer upper bound for 10 ^ 30 t ξ tilde, BJS display 31, odd n, ε = 1/100000. -/
def tilNat1122e (T CP CC : ℕ) : ℕ :=
  cdiv1122e (9214 * 10 ^ 6 * T + 500004 * T + 6 * (10 ^ 5 + 1) * 10 ^ 5 * CP +
    2 * (2 * 10 ^ 5 + 1) * 10 ^ 5 * CC) (10 ^ 10)

/-- Scaled decimal upper bounds for γ: 1, e ^ 0.2, e ^ 0.4, e ^ 0.6, e ^ 0.8, 4 e / 3. -/
def g0e : ℕ := 10 ^ 30
def g1e : ℕ := 1221402758161 * 10 ^ 18
def g2e : ℕ := 1491824697642 * 10 ^ 18
def g3e : ℕ := 1822118800391 * 10 ^ 18
def g4e : ℕ := 2225540928493 * 10 ^ 18
def g5e : ℕ := 3624375771467 * 10 ^ 18

/-- Integer upper bound for 10 ^ 30 τ_n from T ≥ 10 ^ 30 τ_(n-1), n ≥ 2, display 31. -/
def stepNat1122e (n T : ℕ) : ℕ :=
  let CP := cpow1122e (n - 1) (n - 2)
  let CC := cpow1122e n (n - 1)
  if n % 2 = 0 then
    max (max (max (brNat1122e 9607 g0e T CP CC) (brNat1122e 9557 g1e T CP CC))
      (max (brNat1122e 9457 g2e T CP CC) (brNat1122e 9261 g3e T CP CC)))
      (max (brNat1122e 8914 g4e T CP CC) (brNat1122e 8349 g5e T CP CC))
  else max (brNat1122e 8349 g5e T CP CC) (tilNat1122e T CP CC)

/-- The certified table: entry n - 1 bounds 10 ^ 30 τ_n, 1 ≤ n ≤ 500. -/
def tauList1122e : List ℕ :=
[
  3000000000000000000000000000000, 10413585321207144010000000000000, 12184021040391756976497357604000,
  12198334885993103627947539674256, 12057520546117879292369501884023, 11811033425260794369438665948805,
  11295964998746061321823576486302, 10965007632130111525900246925255, 10312869970469453244154827139637,
  9969506139856639208229300576745, 9295964423425803080732174499734, 8962924015074965511057803957640,
  8315006634991586839851028857111, 8005229051319286474273256882150, 7410505340546008748094432231572,
  7129297692827845491968483957556, 6586261151401709847672054997571, 6331853915681031452569852901507,
  5842580959160800498412797202878, 5615554335966928950028311703120, 5179215637657684273282245544820,
  4977275484994444190880624510865, 4588960262382973051733407151113, 4409398380937646135654183853565,
  4064265391096347660195314882221, 3904940484868809641429361677755, 3598855552570201158852960676352,
  3457709361617955960028847496204, 3186496623799297530226915764707, 3061433702233639828847462398096,
  2821143922809870010728079556584, 2710377756224675172369971243967, 2497566061392208187123663978248,
  2399484240201074491740112655477, 2211055252961408850717015255413, 2124222533445423200945140010682,
  1957398190618219432666448560825, 1880519836318122783212877472124, 1732821338726912326399671268602,
  1664759853326522292724831889957, 1534000971565319283069554204324, 1473746975253810425529619020934,
  1357988072922451180508539598748, 1304646828438584407058912647980, 1202168742359403432423215333339,
  1154947601455031804399673080740, 1064227685239226966349645388712, 1022424895459296079620192810647,
  942114323143969562420349325564, 905107950265763325805771939969, 834012176242983940555185475920,
  801251975203025062888002196858, 738313862291549874111864566736, 709312666640754880242449626386,
  653596272610582379695272889134, 627922785926157247104002841171, 578599509642361582321651400730,
  555871909527774089625865172499, 512208200645511727978155181846, 492088469298875517684813427863,
  453434935047176059800920879118, 435623836667962106276301615749, 401405591940130187138706503104,
  385638224587692949981153436297, 355346345965298009992359998757, 341388202878762106037115723451,
  314572161576982472968707929071, 302215643964666374157653412703, 278476606208804959239845829938,
  267537935938397774438363008025, 246522831659712614396657754217, 236839318081114119412640241463,
  218235589983686007271894306719, 209663210309317004926907588071, 193194165345936017133258805598,
  185605422639502979127234682136, 171026116827189935955568588135, 164308143761923172505270813917,
  151401739166289526963049765495, 145454619359508340750308664802, 134029159082699572269653132683,
  128764441044783764999953472466, 118649994265597471471940641423, 113989375868280775670042648034,
  105035510452217290911354933739, 100909674326267108065959446192, 92983219454935220014067113234,
  89330802054190039583031183374, 82313867592004033006984816579, 79080546524599149875946636069,
  72868769628506520092685100961, 70006455720569465032464936435, 64507448652645319690085449496,
  61973570718399811038048031579, 57105546763737937763013255418, 54862418444512035464080438145,
  50552975497888897919645169164, 48567234753081710639364071703, 44752278482782762906134152958,
  42994391396369516266851350750, 39617181969449179262714879858, 38061003492155314152387819685,
  35071311683105509460315745106, 33693696777177282383230612895, 31047056908825419008381032585,
  29827516311958393316660455116, 27484564917594364744558143183, 26404960406199838486075561318,
  24330850776859644743789005494, 23375125396321586805307242078, 21539009305793074701549356290,
  20692948555431562390558727997, 19067517454680887747803521234, 18318537875527024029318556522,
  16879616732732462853411321943, 16216578753781543016440057693, 14942766499158982373673255264,
  14355808758564880456166556740, 13228159986322113033889379162, 12708552663392556135398259110,
  11710295856766585453372094011, 11250310833366548356530490304, 10366598921905778806079575651,
  9959394842179957030161409603, 9177084381310504479326967725, 8816604900218473019480424366,
  8124060588832966954915037930, 7804944296147800236139588233, 7191865924807375001334553899,
  6909366604877634746144651358, 6366635860828246680725584834, 6116551902127020822354745923,
  5636096752661565913015047505, 5414708657230996314303098159, 4989383294371385957813178041,
  4793398357740843491925716769, 4416876918657660066600737865, 4243380257460158282799133842,
  3910062739934015205580847427, 3756473938854750364778873289, 3461402912460299430276726063,
  3325437645727514308326347235, 3064224519985793185665396679, 2943860576600514893872883103,
  2712620329486088714833507486, 2606067536884085671909366441, 2401360932904267775399894729,
  2307034531724941510899467028, 2125816970180761177377060772, 2042314044145991599931544158,
  1881890276795249582323928521, 1807968887139853399566251624, 1665952931778205472430887609,
  1600513645898455373348789421, 1474793299653337163450757086, 1416862839249187316276834160,
  1305568263792908788966802273, 1254285029302795661313766116, 1155760940752775074193189937,
  1110362196785956353537153733, 1023143246672564360864966629, 982953777847970090503654476,
  905742758991193551129048788, 870164827461115184928206076, 801813380612110518185928665,
  770317835909008236485926622, 709809370206482773899162657, 681927779189689639399814306,
  628362352407110629914106970, 603680032258154828380305136, 556260965965748779521174423,
  534410816612054542924231376, 492432847180941985225921583, 473089891417565641937042020,
  435928680635951817331762638, 418805230740600140018422513, 385908080033448091317174013,
  370749458987858797145402881, 341627089132662272225271906, 328207842812085269036128836,
  302427116890479108278432618, 290547660885164150947038080, 267725142238853571244347441,
  257208793435730503096453223, 237005042814237389452588253, 227695391589512318799615842,
  209809918671234282793746838, 201568502610530162370545335, 185735296811100419160569671,
  178439541358388747933482957, 164423115456063128326673020, 157964510862664594413194562,
  145556398597588094867108969, 139838886057010185648609042, 128854541613167589988717473,
  123793084578767513079098512, 114069137834622558758243678, 109588457271307415643554651,
  100980283996481601053277102, 97013738755848193146635360, 89393309615381813077306796,
  85881905282118936614577750, 79135881656561256256350439, 76027393124690039082027340,
  70055441425156593762010207, 67303636154187962672497126, 62016935561197952666247718,
  59580885959698421534722126, 54900807391396464907049102, 52744282101045106946689515,
  48601218763105726636445117, 46692143789811959793614991, 43024475913799087867751328,
  41334457591286025573264528, 38087635964024291300999020, 36591538654916483277149302,
  33717273308209408977695828, 32392845561774533266754212, 29848387555854281903360492,
  28675931162244016259463708, 26423436780920121247180451, 25385513799754923982983557,
  23391481700938380224022179, 22472655106873212180039164, 20707428057217383406046383,
  19894032145110658099425207, 18331355928069828763759631, 17611293062992366158476453,
  16227925999938833021925085, 15590486689086317684862495, 14365853965894782106351084,
  13801557576333826468564250, 12717445234233427429992069, 12217898987476761346805005,
  11258183026897621338004187, 10815957173135153201082201, 9966363741511769786391266,
  9574881056964237055056296, 8822774153769648657167329, 8476212117659334426441879,
  7810405659207678554308614, 7503609855424576872077704, 6914201304282420300945842,
  6642608759769094248533516, 6120831844346275399218857, 5880403164013438873451313,
  5418497497832344515547098, 5205656786647973374865018, 4796752448139037780928571,
  4608334126852424258251853, 4246349483031499983507150, 4079551206522675832775500,
  3759102460882140128720065, 3611443438891422537782875, 3327764558211078672996610,
  3197048658553076125767389, 2945920487702551459509602, 2830203573198843571077346,
  2607891083656155837848768, 2505452096988946159668829, 2308648835772645277622431,
  2217964202204503312467832, 2043743115008525258155296, 1963464082259946187664534,
  1809233979383813047527474, 1738166557644662973182072, 1601633575236941319696496,
  1538720778959639196540883, 1417854262387847849236463, 1362160389744528067294254,
  1255162691674959543506112, 1205859407867029304378096, 1111139151861417915666019,
  1067493169298614738401421, 983641581277205818419446, 945003753393495731930048,
  870773708942438143544352, 836569375441111558887744, 770856851334839996113567,
  740577291267664906474112, 682404945334820744577647, 655599810896925469146089,
  604102446013211897903444, 580373064521551651361525, 534784760535532994955708,
  513778204971286368449385, 473420927176303106196211, 454824767102393539897708,
  419098281828430434179711, 402635936612584928151976, 371008883952720756690683,
  356435509184566491948620, 328437500080692997679893, 315536346001585845018683,
  290750966149375815293110, 279330153933898636563706, 257388770454122960235197,
  247278438396898221886840, 227854717159733241916399, 218904494322795076398763,
  201709546381301320876769, 193786316127592077141315, 178564401073284245932912,
  171550321223316018951963, 158075043559844674152623, 151865793725321856332956,
  139936735688944142008142, 134439965715945290355019, 123879706462733774084021,
  119013662908152951583632, 109665139734323002400009, 105357449947158879276801,
  97081622295952529288482, 93268218019089951628691, 85941999530997723135904,
  82566164014214316889025, 76080591863924247903088, 73092116315836700923230,
  67350730608464574592055, 64705167441326956975506, 59622576564692791481621,
  57280578325559068707960, 52781188920998635191184, 50707923077174562848415,
  46724815739745670167552, 44889446614635874523327, 41363380601012005225385,
  39738610755195677462418, 36617142896270501299834, 35178807132767837774474,
  32415511846560446970407, 31142217801931396915158, 28695996606046572808255,
  27568806581834397252048, 25403276835858827980644, 24405426138258496725049,
  22488379924860462262610, 21605027523478632834778, 19907952620151397235008,
  19125960417406470632122, 17623616234269576530942, 16931353662506287496868,
  15601395839088960079002, 14988566879180980965142, 13811214956816741662013,
  13268705005505502020554, 12226448232630526839052, 11746188541058644321021,
  10823525435856963226039, 10398373103091005418738, 9581580900002556184343,
  9205212636689162076422, 8482143187759313450005, 8148961269861854828283,
  7508860365373790639477, 7213909379239784551263, 6647256800386063226468,
  6386149940894976111214, 5884517865592135714047, 5653371691216155445494,
  5209299347132475111747, 5004676021522468066299, 4611558722033748608311,
  4430414883089685203718, 4082405795795156384212, 3922047291750844893948,
  3613970478552634944239, 3472012297864689372448, 3199285733256222941399,
  3073616532334625334570, 2832183954949187127484, 2720934656150488762090,
  2507205239998241732299, 2408721232839451477750, 2219516180963401057319,
  2132332713105299545175, 1964837979343811351154, 1887658371333860559167,
  1739382807020649160788, 1671059166783434902642, 1539797469901019757763,
  1479313620142902030582, 1363113535872402524147, 1309569900479714955149,
  1206703185320861305624, 1159303409967106042445, 1068240127577911226808,
  1026279235548280735704, 945665002006474978144, 908518909081314852462,
  837154749136385134444, 804270981588491515768, 741095496306423899850,
  711984973960977520644, 656058554541136725992, 630288316687748940733,
  580779169664041588124, 557965935633424356579, 514137711612605247634,
  493942180244341449758, 455143022183725300988, 437264825401140852966,
  402917673540787169136, 387090908977459347607, 356684918232116279454,
  342674194466785886780, 315757136628489533171, 303354072209167769316,
  279525609958479269930, 268545734145745490529, 247451466836015475917,
  237731475970270321473, 219057668627898178120, 210452997314530566924,
  193921914459655389828, 186304585448367743475, 171670360335920291415,
  164927081115473730356, 151972058959824101293, 146002536758863039388,
  134534037554855362358, 129249487687823884671, 119096940481645113616,
  114418765854428484271, 105431171842330633184, 101289793977913351881,
  93333480701464175692, 89667304899452747200, 82623938135467655878,
  79378437374298799121, 73143261150299003410, 70270165107013626493,
  64750443665965772185, 62207020791842275934, 57320659333525873487,
  55069081307885859105, 50743404993179057406, 48750184102888821716,
  44920857161106978422, 43156348237921831999, 39766417101095611401,
  38204376609162655059, 35203422841794679158, 33820618557623807340,
  31164008983450704707, 29939874463125230534, 27588097336022693471,
  26504426030541469019, 24422503376444207050, 23463177845773651659,
  21620145235373402470, 20770897433810857724, 19139343448693373834,
  18387542516266722778, 16943201058968988721, 16277665462694670674,
  14999054847111070488, 14409886078087992729, 13277989532418135342,
  12756424885334864750, 11754407715694381089, 11292689961139673536,
  10405649169209228175, 9996911180422566198, 9211653811199138106,
  8849816429315288164, 8154663352332498861, 7834344971070180844,
  7218957176726356138, 6935393701774374420, 6390618529274154801,
  6139592521931184000, 5657327531789326516, 5435105483010921782,
  5008177949494456080, 4811454751424379698, 4433514982624576584,
  4259364771735695049, 3924791670619602122, 3770624311354537602,
  3474441773205888408, 3337964334898744246, 3075767237727633630,
  2954949891853167759, 2722838579030081399, 2615884409570218247,
  2410406690244831378, 2315724968162185140, 2133824772839335495,
  2050007297169070675, 1888979224796443103, 1814779378477603477,
  1672228459024099486, 1606542667967848466, 1480348742041591047,
  1422200061677141733, 1310486247401282285, 1259009832582264693,
  1160114610736531745, 1114544852901758763]

/-- 10 ^ 30 τ_n upper bound from the table. -/
def tauTab1122e (n : ℕ) : ℕ := tauList1122e.getD (n - 1) 0

theorem tauTab_one1122e : tauTab1122e 1 = 3 * tauS1122e := by decide +kernel

/-- The step check of the certificate, steps 2 to 101, in chunks to keep memory low. -/
theorem tauTab_steps0_1122e :
    ∀ n, n < 100 → stepNat1122e (n + 0 + 2) (tauTab1122e (n + 0 + 1)) ≤
      tauTab1122e (n + 0 + 2) := by
  decide +kernel

/-- The step check of the certificate, steps 102 to 201, in chunks to keep memory low. -/
theorem tauTab_steps1_1122e :
    ∀ n, n < 100 → stepNat1122e (n + 100 + 2) (tauTab1122e (n + 100 + 1)) ≤
      tauTab1122e (n + 100 + 2) := by
  decide +kernel

/-- The step check of the certificate, steps 202 to 301, in chunks to keep memory low. -/
theorem tauTab_steps2_1122e :
    ∀ n, n < 100 → stepNat1122e (n + 200 + 2) (tauTab1122e (n + 200 + 1)) ≤
      tauTab1122e (n + 200 + 2) := by
  decide +kernel

/-- The step check of the certificate, steps 302 to 401, in chunks to keep memory low. -/
theorem tauTab_steps3_1122e :
    ∀ n, n < 100 → stepNat1122e (n + 300 + 2) (tauTab1122e (n + 300 + 1)) ≤
      tauTab1122e (n + 300 + 2) := by
  decide +kernel

/-- The step check of the certificate, steps 402 to 500, in chunks to keep memory low. -/
theorem tauTab_steps4_1122e :
    ∀ n, n < 99 → stepNat1122e (n + 400 + 2) (tauTab1122e (n + 400 + 1)) ≤
      tauTab1122e (n + 400 + 2) := by
  decide +kernel

/-- The step check of the certificate, 499 steps. -/
theorem tauTab_steps1122e :
    ∀ n, n < 499 → stepNat1122e (n + 2) (tauTab1122e (n + 1)) ≤ tauTab1122e (n + 2) := by
  intro n hn
  rcases Nat.lt_or_ge n 100 with h | h
  · exact tauTab_steps0_1122e n h
  rcases Nat.lt_or_ge n 200 with h | h
  · have := tauTab_steps1_1122e (n - 100) (by omega)
    rwa [show n - 100 + 100 = n by omega] at this
  rcases Nat.lt_or_ge n 300 with h | h
  · have := tauTab_steps2_1122e (n - 200) (by omega)
    rwa [show n - 200 + 200 = n by omega] at this
  rcases Nat.lt_or_ge n 400 with h | h
  · have := tauTab_steps3_1122e (n - 300) (by omega)
    rwa [show n - 300 + 300 = n by omega] at this
  have := tauTab_steps4_1122e (n - 400) (by omega)
  rwa [show n - 400 + 400 = n by omega] at this

theorem tauTab_odd_sum1122e :
    ∑ n ∈ (Finset.Icc 1 500).filter Odd, tauTab1122e n ≤ 131508 * 10 ^ 27 := by
  decide +kernel

theorem tauTab_even_sum1122e :
    ∑ n ∈ (Finset.Icc 1 500).filter Even, tauTab1122e n ≤ 134837 * 10 ^ 27 := by
  decide +kernel

theorem tauTab_500_1122e : tauTab1122e 500 * 10 ^ 12 ≤ 2 * tauS1122e := by
  decide +kernel

theorem cdiv_ge1122e (a b : ℕ) (hb : 0 < b) : (a : ℝ) / b ≤ (cdiv1122e a b : ℝ) := by
  have h : a ≤ b * cdiv1122e a b := by
    unfold cdiv1122e
    have h1 := Nat.div_add_mod (a + b - 1) b
    have h2 := Nat.mod_lt (a + b - 1) hb
    generalize (a + b - 1) / b = q at *
    generalize (a + b - 1) % b = r at *
    omega
  rw [div_le_iff₀ (by exact_mod_cast hb)]
  exact_mod_cast (by linarith [h] : a ≤ cdiv1122e a b * b)

theorem exp_taylor_le1122e (x u : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1)
    (h : ∑ m ∈ range 16, x ^ m / (m.factorial : ℝ) + x ^ 16 * ((17 : ℝ) / (Nat.factorial 16 * 16)) ≤ u) :
    exp x ≤ u := by
  have hb := Real.exp_bound (x := x) (by rw [abs_of_nonneg hx0]; exact hx) (n := 16) (by norm_num)
  rw [abs_of_nonneg hx0] at hb
  have := (abs_le.mp hb).2
  push_cast at this h ⊢
  linarith

theorem exp02_1122e : exp 0.2 ≤ 1.221402758161 := by
  apply exp_taylor_le1122e _ _ (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num
theorem exp08_1122e : exp 0.8 ≤ 2.225540928493 := by
  apply exp_taylor_le1122e _ _ (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num
theorem e43_1122e : 4 * exp 1 / 3 ≤ 3.624375771467 := by
  have := Real.exp_one_lt_d9; linarith

theorem mulXi1122e (γ κ ε cp cc t : ℝ) (ht : 0 < t) :
    t * bjsXi306 γ κ ε cp cc t = κ * t + (γ + κ) * ε * t + 2 * γ * cp + 2 * cc := by
  unfold bjsXi306; field_simp

theorem br_sound1122e (S k g T CP CC : ℕ) (hS : 0 < S) (κ γ t cp cc : ℝ)
    (hκ : κ = (k : ℝ) / 10000) (hγ0 : 0 ≤ γ) (hγ : γ ≤ g / S) (ht : 0 < t) (htT : t ≤ T / S)
    (hcp0 : 0 ≤ cp) (hcp : cp ≤ CP / S) (hcc : cc ≤ CC / S) :
    t * bjsXi306 γ κ (1 / 100000) cp cc t ≤
      (cdiv1122e (k * T * S * 10 ^ 5 + (g * 10 ^ 4 + k * S) * T +
        2 * g * CP * 10 ^ 9 + 2 * CC * S * 10 ^ 9) (S * 10 ^ 9) : ℝ) / S := by
  have hSr : (0 : ℝ) < S := by exact_mod_cast hS
  rw [mulXi1122e _ _ _ _ _ _ ht]
  refine le_trans ?_ (div_le_div_of_nonneg_right (cdiv_ge1122e _ _ (by positivity)) hSr.le)
  push_cast
  rw [le_div_iff₀ hSr, le_div_iff₀ (by positivity)]
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hκ0 : 0 ≤ κ := by rw [hκ]; positivity
  have e1 : γ * S ≤ g := by rwa [le_div_iff₀ hSr] at hγ
  have e2 : t * S ≤ T := by rwa [le_div_iff₀ hSr] at htT
  have e3 : cp * S ≤ CP := by rwa [le_div_iff₀ hSr] at hcp
  have e4 : cc * S ≤ CC := by rwa [le_div_iff₀ hSr] at hcc
  have hg0 : (0:ℝ) ≤ g := le_trans (by positivity) e1
  have hT0 : (0:ℝ) ≤ T := le_trans (by positivity) e2
  subst hκ
  have a1 : (γ * S) * (t * S) ≤ g * T := mul_le_mul e1 e2 (by positivity) hg0
  have a2 : (γ * S) * (cp * S) ≤ g * CP := mul_le_mul e1 e3 (by positivity) hg0
  nlinarith [mul_le_mul_of_nonneg_left e2 hk0, mul_le_mul_of_nonneg_left e2 hSr.le,
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e2 hk0) hSr.le,
    mul_le_mul_of_nonneg_left e4 hSr.le]

theorem exp04_1122e : exp 0.4 ≤ 1.491824697642 := by
  apply exp_taylor_le1122e _ _ (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num
theorem exp06_1122e : exp 0.6 ≤ 1.822118800391 := by
  apply exp_taylor_le1122e _ _ (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num

theorem til_sound1122e (S T CP CC : ℕ) (hS : 0 < S) (t cp cc : ℝ)
    (ht : 0 < t) (htT : t ≤ T / S) (_hcp0 : 0 ≤ cp) (hcp : cp ≤ CP / S) (hcc : cc ≤ CC / S) :
    t * (0.9214 + (5 + 4 * (1 / 100000)) * (1 / 100000) + 6 * (1 + 1 / 100000) * cp / t +
      2 * (2 + 1 / 100000) * cc / t) ≤
      (cdiv1122e (9214 * 10 ^ 6 * T + 500004 * T + 6 * (10 ^ 5 + 1) * 10 ^ 5 * CP +
        2 * (2 * 10 ^ 5 + 1) * 10 ^ 5 * CC) (10 ^ 10) : ℝ) / S := by
  have hSr : (0 : ℝ) < S := by exact_mod_cast hS
  refine le_trans ?_ (div_le_div_of_nonneg_right (cdiv_ge1122e _ _ (by positivity)) hSr.le)
  have e2 : t * S ≤ T := by rwa [le_div_iff₀ hSr] at htT
  have e3 : cp * S ≤ CP := by rwa [le_div_iff₀ hSr] at hcp
  have e4 : cc * S ≤ CC := by rwa [le_div_iff₀ hSr] at hcc
  have hexp : t * (0.9214 + (5 + 4 * (1 / 100000)) * (1 / 100000) + 6 * (1 + 1 / 100000) * cp / t +
      2 * (2 + 1 / 100000) * cc / t) = 0.9214 * t + (5 + 4 * (1 / 100000)) * (1 / 100000) * t +
      6 * (1 + 1 / 100000) * cp + 2 * (2 + 1 / 100000) * cc := by
    field_simp
  rw [hexp]
  push_cast
  rw [le_div_iff₀ hSr, le_div_iff₀ (by positivity)]
  nlinarith

/-- c_n of Table 2 as 100 c_n / 100 for 1 ≤ n ≤ 500. -/
theorem bjsC_eq1122e (n : ℕ) (hn : n ≤ 500) : bjsC306 n = (aN1122e n : ℝ) / 100 := by
  unfold bjsC306 aN1122e
  by_cases h0 : n ≤ 1
  · rw [if_pos h0, if_pos h0]; norm_num
  rw [if_neg h0, if_neg h0]
  by_cases h1 : n = 2
  · rw [if_pos h1, if_pos h1]; norm_num
  rw [if_neg h1, if_neg h1]
  by_cases h2 : n = 3
  · rw [if_pos h2, if_pos h2]; norm_num
  rw [if_neg h2, if_neg h2]
  by_cases h3 : n = 4
  · rw [if_pos h3, if_pos h3]; norm_num
  rw [if_neg h3, if_neg h3]
  by_cases h4 : n = 5
  · rw [if_pos h4, if_pos h4]; norm_num
  rw [if_neg h4, if_neg h4]
  by_cases h5 : n = 6
  · rw [if_pos h5, if_pos h5]; norm_num
  rw [if_neg h5, if_neg h5]
  by_cases h6 : n = 7
  · rw [if_pos h6, if_pos h6]; norm_num
  rw [if_neg h6, if_neg h6]
  by_cases h7 : n = 8
  · rw [if_pos h7, if_pos h7]; norm_num
  rw [if_neg h7, if_neg h7]
  by_cases h8 : n ≤ 10
  · rw [if_pos h8, if_pos h8]; norm_num
  rw [if_neg h8, if_neg h8]
  by_cases h9 : n ≤ 12
  · rw [if_pos h9, if_pos h9]; norm_num
  rw [if_neg h9, if_neg h9]
  by_cases h10 : n = 13
  · rw [if_pos h10, if_pos h10]; norm_num
  rw [if_neg h10, if_neg h10]
  by_cases h11 : n = 14
  · rw [if_pos h11, if_pos h11]; norm_num
  rw [if_neg h11, if_neg h11]
  by_cases h12 : n ≤ 18
  · rw [if_pos h12, if_pos h12]; norm_num
  rw [if_neg h12, if_neg h12]
  by_cases h13 : n ≤ 20
  · rw [if_pos h13, if_pos h13]; norm_num
  rw [if_neg h13, if_neg h13]
  by_cases h14 : n ≤ 26
  · rw [if_pos h14, if_pos h14]; norm_num
  rw [if_neg h14, if_neg h14]
  by_cases h15 : n ≤ 34
  · rw [if_pos h15, if_pos h15]; norm_num
  rw [if_neg h15, if_neg h15]
  by_cases h16 : n ≤ 46
  · rw [if_pos h16, if_pos h16]; norm_num
  rw [if_neg h16, if_neg h16]
  by_cases h17 : n ≤ 82
  · rw [if_pos h17, if_pos h17]; norm_num
  rw [if_neg h17, if_neg h17]
  by_cases h18 : n ≤ 345
  · rw [if_pos h18, if_pos h18]; norm_num
  rw [if_neg h18, if_neg h18]
  rw [if_pos hn]; norm_num

theorem cpow_ge1122e (n k : ℕ) (hn : n ≤ 500) :
    bjsC306 n ^ k ≤ (cpow1122e n k : ℝ) / tauS1122e := by
  have hS : (0 : ℝ) < tauS1122e := by unfold tauS1122e; positivity
  rw [bjsC_eq1122e n hn, le_div_iff₀ hS, div_pow]
  have := cdiv_ge1122e (aN1122e n ^ k * tauS1122e) (100 ^ k) (by positivity)
  unfold cpow1122e
  push_cast at this ⊢
  rw [div_mul_eq_mul_div]
  exact this

theorem gam_bounds1122e :
    (1 : ℝ) ≤ g0e / tauS1122e ∧ exp 0.2 ≤ g1e / tauS1122e ∧ exp 0.4 ≤ g2e / tauS1122e ∧
    exp 0.6 ≤ g3e / tauS1122e ∧ exp 0.8 ≤ g4e / tauS1122e ∧
    4 * exp 1 / 3 ≤ g5e / tauS1122e := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [g0e, tauS1122e]
  · have h : (g1e : ℝ) / tauS1122e = 1.221402758161 := by norm_num [g1e, tauS1122e]
    rw [h]; exact exp02_1122e
  · have h : (g2e : ℝ) / tauS1122e = 1.491824697642 := by norm_num [g2e, tauS1122e]
    rw [h]; exact exp04_1122e
  · have h : (g3e : ℝ) / tauS1122e = 1.822118800391 := by norm_num [g3e, tauS1122e]
    rw [h]; exact exp06_1122e
  · have h : (g4e : ℝ) / tauS1122e = 2.225540928493 := by norm_num [g4e, tauS1122e]
    rw [h]; exact exp08_1122e
  · have h : (g5e : ℝ) / tauS1122e = 3.624375771467 := by norm_num [g5e, tauS1122e]
    rw [h]; exact e43_1122e

theorem mul_max_le1122e {t a b X : ℝ} (ht : 0 ≤ t) (ha : t * a ≤ X) (hb : t * b ≤ X) :
    t * max a b ≤ X := by
  rw [mul_max_of_nonneg _ _ ht]; exact max_le ha hb

theorem brb1122e (k g T CP CC X : ℕ) (hX : brNat1122e k g T CP CC ≤ X) (κ γ t cp cc : ℝ)
    (hκ : κ = (k : ℝ) / 10000) (hγ0 : 0 ≤ γ) (hγ : γ ≤ g / tauS1122e) (ht : 0 < t)
    (htT : t ≤ T / tauS1122e) (hcp0 : 0 ≤ cp) (hcp : cp ≤ CP / tauS1122e)
    (hcc : cc ≤ CC / tauS1122e) :
    t * bjsXi306 γ κ (1 / 100000) cp cc t ≤ (X : ℝ) / tauS1122e := by
  have hS : 0 < tauS1122e := by unfold tauS1122e; positivity
  refine (br_sound1122e tauS1122e k g T CP CC hS κ γ t cp cc hκ hγ0 hγ ht htT hcp0 hcp hcc).trans ?_
  exact div_le_div_of_nonneg_right (by exact_mod_cast hX) (by positivity)

theorem xi_pos1122e {γ κ cp cc t : ℝ} (hγ : 0 ≤ γ) (hκ : 0 < κ)
    (hcp : 0 ≤ cp) (hcc : 0 ≤ cc) (ht : 0 < t) : 0 < t * bjsXi306 γ κ (1 / 100000) cp cc t := by
  rw [mulXi1122e _ _ _ _ _ _ ht]; positivity

/-- τ_n of BJS display 31 at ε = 1/100000 is positive and at most the table value. -/
theorem tau_le_tab1122e (n : ℕ) (hn1 : 1 ≤ n) (hn : n ≤ 500) :
    0 < bjsTau306 bjsC306 (1 / 100000) n ∧
      bjsTau306 bjsC306 (1 / 100000) n ≤ (tauTab1122e n : ℝ) / tauS1122e := by
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_ge m 1 with h0 | h1
    · have : m = 0 := by omega
      subst this
      refine ⟨by simp [bjsTau306], ?_⟩
      rw [tauTab_one1122e]
      simp only [bjsTau306]
      have hS : (0 : ℝ) < tauS1122e := by unfold tauS1122e; positivity
      push_cast
      rw [mul_div_assoc, div_self hS.ne']; norm_num
    · obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
      obtain ⟨htp, htT⟩ := ih (by omega) (by omega)
      have hstep := tauTab_steps1122e n (by omega)
      have hcp := cpow_ge1122e (n + 1) n (by omega)
      have hcc := cpow_ge1122e (n + 2) (n + 1) (by omega)
      have hcp0 : 0 ≤ bjsC306 (n + 1) ^ n := pow_nonneg (bjsC306_pos _).le _
      have hcc0 : 0 ≤ bjsC306 (n + 2) ^ (n + 1) := pow_nonneg (bjsC306_pos _).le _
      obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5⟩ := gam_bounds1122e
      unfold stepNat1122e at hstep
      simp only [show n + 2 - 1 = n + 1 by omega, show n + 2 - 2 = n by omega] at hstep
      simp only [bjsTau306]
      set t := bjsTau306 bjsC306 (1 / 100000) (n + 1)
      set T := tauTab1122e (n + 1)
      set X := tauTab1122e (n + 2)
      have hp : 0 < t * bjsXi306 (4 * exp 1 / 3) 0.8349 (1 / 100000) (bjsC306 (n + 1) ^ n)
          (bjsC306 (n + 2) ^ (n + 1)) t := xi_pos1122e (by positivity) (by norm_num) hcp0 hcc0 htp
      split_ifs with he
      · rw [if_pos (Nat.even_iff.mp he)] at hstep
        refine ⟨lt_of_lt_of_le hp (mul_le_mul_of_nonneg_left
          ((le_max_right _ _).trans (le_max_right _ _)) htp.le), ?_⟩
        refine mul_max_le1122e htp.le (mul_max_le1122e htp.le (mul_max_le1122e htp.le ?_ ?_)
          (mul_max_le1122e htp.le ?_ ?_)) (mul_max_le1122e htp.le ?_ ?_)
        · exact brb1122e 9607 g0e T _ _ X (by omega) _ _ _ _ _ (by norm_num) (by positivity) hg0 htp htT hcp0 hcp hcc
        · exact brb1122e 9557 g1e T _ _ X (by omega) _ _ _ _ _ (by norm_num) (by positivity) hg1 htp htT hcp0 hcp hcc
        · exact brb1122e 9457 g2e T _ _ X (by omega) _ _ _ _ _ (by norm_num) (by positivity) hg2 htp htT hcp0 hcp hcc
        · exact brb1122e 9261 g3e T _ _ X (by omega) _ _ _ _ _ (by norm_num) (by positivity) hg3 htp htT hcp0 hcp hcc
        · exact brb1122e 8914 g4e T _ _ X (by omega) _ _ _ _ _ (by norm_num) (by positivity) hg4 htp htT hcp0 hcp hcc
        · exact brb1122e 8349 g5e T _ _ X (by omega) _ _ _ _ _ (by norm_num) (by positivity) hg5 htp htT hcp0 hcp hcc
      · rw [if_neg (fun h => he (Nat.even_iff.mpr h))] at hstep
        refine ⟨lt_of_lt_of_le hp (mul_le_mul_of_nonneg_left (le_max_left _ _) htp.le), ?_⟩
        refine mul_max_le1122e htp.le ?_ ?_
        · exact brb1122e 8349 g5e T _ _ X (by omega) _ _ _ _ _ (by norm_num) (by positivity) hg5 htp htT hcp0 hcp hcc
        · refine (til_sound1122e tauS1122e T _ _ (by unfold tauS1122e; positivity) t _ _ htp htT hcp0 hcp hcc).trans ?_
          exact div_le_div_of_nonneg_right (by exact_mod_cast (by unfold tilNat1122e at hstep; omega)) (by positivity)

/-- Sums of the table bounds over a filter of Icc 1 N, N ≤ 500. -/
theorem tau_sum_le_tab1122e (p : ℕ → Prop) [DecidablePred p] (N : ℕ) (hN : N ≤ 500) :
    ∑ n ∈ (Finset.Icc 1 N).filter p, bjsTau306 bjsC306 (1 / 100000) n ≤
      ((∑ n ∈ (Finset.Icc 1 500).filter p, tauTab1122e n : ℕ) : ℝ) / tauS1122e := by
  have hS : (0 : ℝ) < tauS1122e := by unfold tauS1122e; positivity
  calc ∑ n ∈ (Finset.Icc 1 N).filter p, bjsTau306 bjsC306 (1 / 100000) n
      ≤ ∑ n ∈ (Finset.Icc 1 N).filter p, (tauTab1122e n : ℝ) / tauS1122e := by
        refine Finset.sum_le_sum fun n hn => ?_
        rw [Finset.mem_filter, Finset.mem_Icc] at hn
        exact (tau_le_tab1122e n hn.1.1 (by omega)).2
    _ ≤ ∑ n ∈ (Finset.Icc 1 500).filter p, (tauTab1122e n : ℝ) / tauS1122e := by
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset_filter _ (Finset.Icc_subset_Icc le_rfl hN)) ?_
        intro i _ _; positivity
    _ = _ := by rw [← Finset.sum_div]; push_cast; rfl

/-- BJS Proposition 13, finite part over odd n, at ε = 1/100000. -/
theorem tau_odd_le500_1122e (N : ℕ) (hN : N ≤ 500) :
    ∑ n ∈ (Finset.Icc 1 N).filter Odd, bjsTau306 bjsC306 (1 / 100000) n ≤ 131.508 := by
  refine (tau_sum_le_tab1122e Odd N hN).trans ?_
  have hS : (0 : ℝ) < tauS1122e := by unfold tauS1122e; positivity
  rw [div_le_iff₀ hS]
  have h := tauTab_odd_sum1122e
  have h2 : ((∑ n ∈ (Finset.Icc 1 500).filter Odd, tauTab1122e n : ℕ) : ℝ) ≤
      ((131508 * 10 ^ 27 : ℕ) : ℝ) := by exact_mod_cast h
  refine h2.trans (le_of_eq ?_)
  norm_num [tauS1122e]

/-- BJS Proposition 13, finite part over even n, at ε = 1/100000. -/
theorem tau_even_le500_1122e (N : ℕ) (hN : N ≤ 500) :
    ∑ n ∈ (Finset.Icc 1 N).filter Even, bjsTau306 bjsC306 (1 / 100000) n ≤ 134.837 := by
  refine (tau_sum_le_tab1122e Even N hN).trans ?_
  have hS : (0 : ℝ) < tauS1122e := by unfold tauS1122e; positivity
  rw [div_le_iff₀ hS]
  have h := tauTab_even_sum1122e
  have h2 : ((∑ n ∈ (Finset.Icc 1 500).filter Even, tauTab1122e n : ℕ) : ℝ) ≤
      ((134837 * 10 ^ 27 : ℕ) : ℝ) := by exact_mod_cast h
  refine h2.trans (le_of_eq ?_)
  norm_num [tauS1122e]

/-- BJS display 31 at n = 500, ε = 1/100000: τ_500 ≤ 2 * 10 ^ -12. -/
theorem tau500_value1122e : bjsTau306 bjsC306 (1 / 100000) 500 ≤ 2e-12 := by
  refine (tau_le_tab1122e 500 (by norm_num) le_rfl).2.trans ?_
  have hS : (0 : ℝ) < tauS1122e := by unfold tauS1122e; positivity
  rw [div_le_iff₀ hS]
  have h2 : ((tauTab1122e 500 * 10 ^ 12 : ℕ) : ℝ) ≤ ((2 * tauS1122e : ℕ) : ℝ) := by
    exact_mod_cast tauTab_500_1122e
  generalize tauTab1122e 500 = x at h2 ⊢
  rw [show (2e-12 : ℝ) * (tauS1122e : ℕ) = 2 * 10 ^ 18 by norm_num [tauS1122e]]
  rw [show ((2 * tauS1122e : ℕ) : ℝ) = 2 * 10 ^ 30 by norm_num [tauS1122e]] at h2
  push_cast at h2
  linarith

end LeanLab.Cai2002

#print axioms LeanLab.Cai2002.tau_le_tab1122e
#print axioms LeanLab.Cai2002.tau_odd_le500_1122e
#print axioms LeanLab.Cai2002.tau_even_le500_1122e
#print axioms LeanLab.Cai2002.tau500_value1122e
