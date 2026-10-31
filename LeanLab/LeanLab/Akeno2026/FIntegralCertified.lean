/-
P0087 Akeno 2026 pages 31 and 36.
The F integral after the page 36 substitution.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Akeno2026.FIntegral
set_option maxRecDepth 4000
namespace LeanLab.Akeno2026.FIntegral
open Real Set MeasureTheory intervalIntegral LeanLab.Akeno2026.SieveFns

def betaQ : ℚ := 21909 / 4000
def xq (k : ℕ) : ℚ :=
  if k ≤ 156 then betaQ - 67 / 19 else if 359 ≤ k then betaQ - 1 else k / 80

def logLq (y : ℚ) : ℚ :=
  2 * ((y + 1) / 2 - 1) / ((y + 1) / 2 + 1) +
  2 * (2 * y / (y + 1) - 1) / (2 * y / (y + 1) + 1)
def logUq (y : ℚ) : ℚ :=
  (((y + 1) / 2 - ((y + 1) / 2)⁻¹) +
    (2 * y / (y + 1) - (2 * y / (y + 1))⁻¹)) / 2

def flq (k : ℕ) : ℚ := if k < 240 then 2 else (ApL k : ℚ) / 1000000000
def fuq (k : ℕ) : ℚ := if k < 240 then 2 else (ApU k : ℚ) / 1000000000
def dlq (k : ℕ) : ℚ :=
  if k < 240 then 0 else (AmL (k - 80) : ℚ) / 1000000000 / (xq (k + 1) - 1)
def duq (k : ℕ) : ℚ :=
  if k < 240 then 0 else (AmU (k - 79) : ℚ) / 1000000000 / (xq k - 1)
def stepL (k : ℕ) : ℚ :=
  let a := xq k
  let b := xq (k + 1)
  flq k * (logLq (b / a) + logLq ((betaQ - a) / (betaQ - b))) +
    dlq k * ((betaQ - a) * logLq ((betaQ - a) / (betaQ - b)) - a * logUq (b / a))
def stepU (k : ℕ) : ℚ :=
  let a := xq k
  let b := xq (k + 1)
  fuq k * (logUq (b / a) + logUq ((betaQ - a) / (betaQ - b))) +
    duq k * ((betaQ - a) * logUq ((betaQ - a) / (betaQ - b)) - a * logLq (b / a))
def tFL : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18392133, 38216135, 57985498, 77701409, 97365039,
   116977542, 136540057, 156053707, 175519600, 194938830, 214312477, 233641606, 252927271, 272170512, 291372356, 310533819, 329655905, 348739607, 367785906, 386795774, 405770171, 424710047, 443616344,
   462489994, 481331919, 500143034, 518924244, 537676446, 556400530, 575097378, 593767864, 612412856, 631033215, 649629795, 668203444, 686755004, 705285311, 723795195, 742285482, 760756991, 779210538,
   797646934, 816066985, 834471492, 852861254, 871237065, 889599715, 907949992, 926288680, 944616560, 962934410, 981243007, 999543124, 1017835533, 1036121003, 1054400302, 1072674196, 1090943450, 1109208827,
   1127471091, 1145731003, 1163989325, 1182246818, 1200504242, 1218762359, 1237021929, 1255283713, 1273548474, 1291816974, 1310089976, 1328368245, 1346652547, 1364943650, 1383242323, 1401549337, 1419865465, 1438191482,
   1456528167, 1474876300, 1493236665, 1511610049, 1529997241, 1548399035, 1566816229, 1585249623, 1603701438, 1622173877, 1640669117, 1659189313, 1677736597, 1696313081, 1714920857, 1733561999, 1752238566, 1770952599,
   1789706127, 1808501165, 1827339717, 1846223775, 1865155323, 1884136336, 1903168781, 1922254621, 1941395811, 1960594304, 1979852050, 1999170996, 2018553089, 2038000276, 2057514504, 2077097724, 2096751888, 2116478954,
   2136280884, 2156159646, 2176117215, 2196155575, 2216276719, 2236482650, 2256775381, 2277156938, 2297629360, 2318194700, 2338855027, 2359612425, 2380468996, 2401426861, 2422488159, 2443655051, 2464929719, 2486314368,
   2507811227, 2529422550, 2551150617, 2572997737, 2594966247, 2617058514, 2639276937, 2661623948, 2684102012, 2706713631, 2729461344, 2752347728, 2775375400, 2798547019, 2821865287, 2845332952, 2868952807, 2892727695,
   2916660509, 2940754193, 2965011747, 2989436226, 3014030743, 3038798472, 3063742649, 3088866576, 3114173621, 3139667223, 3165350893, 3191228216, 3217302856, 3243578558, 3270059149, 3296748545, 3323650750, 3350769863,
   3378110079, 3405675694, 3433471108, 3461500831, 3489769483, 3518281803, 3547042650, 3576057011, 3605330002, 3634866877, 3664673030, 3694754005, 3725115497, 3755763361, 3786703619, 3817942466, 3849486276, 3881341612,
   3913515232, 3946014099, 3978845389, 4012016499, 4045535058, 4079408939, 4113646266, 4148255429, 4183245094, 4218624217, 4254402057, 4290588190, 4327192525, 4364225318, 4401697193, 4439619155, 4478002614, 4484961612]
def tFU : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18392164, 38216205, 57985606, 77701555, 97365222,
   116977762, 136540313, 156053999, 175519927, 194939192, 214312873, 233642036, 252927735, 272171009, 291372886, 310534382, 329656500, 348740234, 367786565, 386796464, 405770891, 424710798, 443617125,
   462490805, 481332760, 500143904, 518925143, 537677374, 556401486, 575098362, 593768876, 612413896, 631034283, 649630890, 668204566, 686756153, 705286487, 723796398, 742286711, 760758247, 779211821,
   797648243, 816068320, 834472853, 852862641, 871238477, 889601153, 907951455, 926290168, 944618073, 962935949, 981244571, 999544713, 1017837147, 1036122642, 1054401966, 1072675885, 1090945164, 1109210566,
   1127472855, 1145732792, 1163991139, 1182248657, 1200506106, 1218764247, 1237023842, 1255285651, 1273550437, 1291818962, 1310091989, 1328370283, 1346654610, 1364945738, 1383244436, 1401551475, 1419867628, 1438193671,
   1456530381, 1474878540, 1493238931, 1511612340, 1529999558, 1548401378, 1566818598, 1585252734, 1603705295, 1622178483, 1640674476, 1659195428, 1677743472, 1696320719, 1714929261, 1733571174, 1752248514, 1770963325,
   1789717634, 1808513457, 1827352797, 1846237647, 1865169990, 1884151802, 1903185050, 1922271696, 1941413696, 1960613003, 1979871567, 1999191335, 2018574253, 2038022269, 2057537330, 2077121387, 2096776392, 2116504303,
   2136307081, 2156186696, 2176145122, 2196184344, 2216306354, 2236513154, 2256806759, 2277189194, 2297662499, 2318228727, 2338889946, 2359648241, 2380505714, 2401464485, 2422526695, 2443694503, 2464970092, 2486355667,
   2507853457, 2529465717, 2551194727, 2573042795, 2595012258, 2617105484, 2639324872, 2661672853, 2684151894, 2706764496, 2729513197, 2752400575, 2775429248, 2798601874, 2821921156, 2845389841, 2869010724, 2892786646,
   2916720501, 2940815234, 2965073844, 2989499386, 3014094974, 3038863782, 3063809046, 3088934068, 3114242217, 3139736931, 3165421721, 3191300173, 3217375952, 3243652801, 3270134550, 3296825113, 3323728495, 3350848795,
   3378190209, 3405757032, 3433553666, 3461584619, 3489854513, 3518368086, 3547130199, 3576145838, 3605420120, 3634958298, 3664765768, 3694848073, 3725210909, 3755860132, 3786801764, 3818042000, 3849587215, 3881443972,
   3913619030, 3946119352, 3978952114, 4012124714, 4045644783, 4079520192, 4113759068, 4148369800, 4183361056, 4218741792, 4254521268, 4290709060, 4327315078, 4364349580, 4401823189, 4439746913, 4478132161, 4485091347]

def FL (k : ℕ) : ℕ := tFL.getD k 0
def FU (k : ℕ) : ℕ := tFU.getD k 0
def chkF (k : ℕ) : Bool := decide
  ((FL (k + 1) : ℚ) / 1000000000 ≤ (FL k : ℚ) / 1000000000 + stepL k ∧
   (FU k : ℚ) / 1000000000 + stepU k ≤ (FU (k + 1) : ℚ) / 1000000000)

theorem chk_F1 : ∀ k < 258, 156 ≤ k → chkF k = true := by decide +kernel
theorem chk_F2 : ∀ k < 359, 258 ≤ k → chkF k = true := by decide +kernel



theorem geometry : ∀ k < 359, 156 ≤ k →
    1 < xq k ∧ xq k ≤ xq (k + 1) ∧ xq (k + 1) < betaQ ∧
    (k < 240 → xq (k + 1) ≤ 3) ∧
    (240 ≤ k → xq k = (k : ℚ) / 80 ∧ xq (k + 1) ≤ (k + 1 : ℚ) / 80) ∧
    0 ≤ flq k ∧ 0 ≤ fuq k ∧ 0 ≤ dlq k ∧ 0 ≤ duq k := by decide +kernel

theorem ap_linear {ωp ωm : ℝ → ℝ} (hω : IsOmegaPair ωp ωm)
    (k : ℕ) (hk : k < 359) (hkl : 156 ≤ k)
    (u : ℝ) (hu : u ∈ Icc (xq k : ℝ) (xq (k + 1) : ℝ)) :
    (flq k : ℝ) + (dlq k : ℝ) * (u - (xq k : ℝ)) ≤ u * ωp u ∧
    u * ωp u ≤ (fuq k : ℝ) + (duq k : ℝ) * (u - (xq k : ℝ)) := by
  obtain ⟨ga, gab, gbt, gc, gg, _⟩ := geometry k hk hkl
  have ha : (1 : ℝ) < (xq k : ℝ) := by exact_mod_cast ga
  have hab : (xq k : ℝ) ≤ (xq (k + 1) : ℝ) := by exact_mod_cast gab
  by_cases hsmall : k < 240
  · have hb : (xq (k + 1) : ℝ) ≤ 3 := by exact_mod_cast gc hsmall
    rw [Ap_two hω (by linarith [hu.2]) (by linarith [hu.1])]
    norm_num [flq, fuq, dlq, duq, hsmall]
  · have hk240 : 240 ≤ k := by omega
    obtain ⟨gk, gq⟩ := gg hk240
    have ep : (xq k : ℝ) = (k : ℝ) / 80 := by
      have h := congrArg (fun x : ℚ => (x : ℝ)) gk
      push_cast at h
      exact h
    have eq : (xq (k + 1) : ℝ) ≤ ((k : ℝ) + 1) / 80 := by
      have h := (Rat.cast_le (K := ℝ)).mpr gq
      push_cast at h
      exact h
    have hp := TB_Ap2 hω k hk240 (by omega)
    have he := TB_Am_upto320 hω (k - 80) (by omega) (by omega)
    have he' := TB_Am_upto320 hω (k - 79) (by omega) (by omega)
    unfold TB at hp he he'
    norm_num only [Nat.cast_ofNat] at hp he he'
    have ej : ((k - 80 : ℕ) : ℝ) / 80 = (xq k : ℝ) - 1 := by
      rw [ep, Nat.cast_sub (by omega)]
      push_cast
      ring
    have ej' : ((k - 79 : ℕ) : ℝ) / 80 = ((k : ℝ) + 1) / 80 - 1 := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [← ep] at hp
    rw [ej] at he
    rw [ej'] at he'
    have hm := Am_mono hω
    have hmono : (xq (k + 1) : ℝ) - 1 ≤ ((k : ℝ) + 1) / 80 - 1 := by linarith
    have heq : ((xq (k + 1) : ℝ) - 1) * ωm ((xq (k + 1) : ℝ) - 1) ≤
        (((k : ℝ) + 1) / 80 - 1) * ωm (((k : ℝ) + 1) / 80 - 1) := by
      apply hm
      · change 1 ≤ (xq (k + 1) : ℝ) - 1
        rw [ep] at hab
        have hkR : (240 : ℝ) ≤ k := by exact_mod_cast hk240
        linarith
      · change 1 ≤ ((k : ℝ) + 1) / 80 - 1
        have hkR : (240 : ℝ) ≤ k := by exact_mod_cast hk240
        linarith
      · exact hmono
    have inc := incr (f := fun x => x * ωp x) (e := fun x => x * ωm x)
      ha hab (fun x hx => (omega_delay hω (by
        rw [ep]
        have hkR : (240 : ℝ) ≤ k := by exact_mod_cast hk240
        linarith) hx.1).2)
      (hm.mono (fun x hx => by
        change 1 ≤ x
        rw [ep] at hx
        have hkR : (240 : ℝ) ≤ k := by exact_mod_cast hk240
        linarith [hx.1]))
      (Am_nonneg hω (by linarith)) u hu
    have hlo : (AmL (k - 80) : ℝ) / 1000000000 / ((xq (k + 1) : ℝ) - 1) ≤
        ((xq k : ℝ) - 1) * ωm ((xq k : ℝ) - 1) / ((xq (k + 1) : ℝ) - 1) :=
      div_le_div_of_nonneg_right he.1 (by linarith)
    have hhi : ((xq (k + 1) : ℝ) - 1) * ωm ((xq (k + 1) : ℝ) - 1) /
        ((xq k : ℝ) - 1) ≤ (AmU (k - 79) : ℝ) / 1000000000 / ((xq k : ℝ) - 1) :=
      div_le_div_of_nonneg_right (heq.trans he'.2) (by linarith)
    have hux : 0 ≤ u - (xq k : ℝ) := by linarith [hu.1]
    simp only [flq, fuq, dlq, duq, ite_eq_right hsmall]
    push_cast
    constructor
    · linarith [mul_le_mul_of_nonneg_right hlo hux, hp.1, inc.1]
    · linarith [mul_le_mul_of_nonneg_right hhi hux, hp.2, inc.2]



theorem step_bounds {ωp ωm : ℝ → ℝ} (hω : IsOmegaPair ωp ωm)
    (k : ℕ) (hk : k < 359) (hkl : 156 ≤ k) :
    (stepL k : ℝ) ≤ (∫ u in (xq k : ℝ)..(xq (k + 1) : ℝ),
      (u * ωp u) * (u⁻¹ + ((betaQ : ℝ) - u)⁻¹)) ∧
    (∫ u in (xq k : ℝ)..(xq (k + 1) : ℝ),
      (u * ωp u) * (u⁻¹ + ((betaQ : ℝ) - u)⁻¹)) ≤ (stepU k : ℝ) := by
  obtain ⟨ga, gab, gbt, _, _, gfl, gfu, gdl, gdu⟩ := geometry k hk hkl
  have ha : (0 : ℝ) < (xq k : ℝ) := by exact_mod_cast (show 0 < xq k by linarith)
  have hab : (xq k : ℝ) ≤ (xq (k + 1) : ℝ) := by exact_mod_cast gab
  have hbt : (xq (k + 1) : ℝ) < (betaQ : ℝ) := by exact_mod_cast gbt
  have h0 : (1 : ℝ) ≤ (xq (k + 1) : ℝ) / (xq k : ℝ) := by
    rw [le_div_iff₀ ha]
    simpa using hab
  have h1 : (1 : ℝ) ≤ ((betaQ : ℝ) - (xq k : ℝ)) /
      ((betaQ : ℝ) - (xq (k + 1) : ℝ)) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  obtain ⟨l0, u0⟩ := log_split_bounds h0
  obtain ⟨l1, u1⟩ := log_split_bounds h1
  have key := both_step ha hab hbt
    ((Ap_mono hω).mono (fun x hx => by
      change 1 ≤ x
      have : (1 : ℝ) < (xq k : ℝ) := by exact_mod_cast ga
      linarith [hx.1]))
    (fun u hu => (ap_linear hω k hk hkl u hu).1)
    (fun u hu => (ap_linear hω k hk hkl u hu).2)
    l0 u0 l1 u1
    (by exact_mod_cast gfl) (by exact_mod_cast gfu)
    (by exact_mod_cast gdl) (by exact_mod_cast gdu)
  dsimp [stepL, stepU, logLq, logUq, logL, logU] at key ⊢
  push_cast
  exact key

noncomputable def fint (ωp : ℝ → ℝ) : ℝ :=
  (∫ u in (xq 156 : ℝ)..(xq 359 : ℝ),
    (u * ωp u) * (u⁻¹ + ((betaQ : ℝ) - u)⁻¹)) / (2 * (betaQ : ℝ))

theorem fint_integrable {ωp ωm : ℝ → ℝ} (hω : IsOmegaPair ωp ωm)
    {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hbt : b < (betaQ : ℝ)) :
    IntervalIntegrable (fun u => (u * ωp u) * (u⁻¹ + ((betaQ : ℝ) - u)⁻¹)) volume a b := by
  have hc : ContinuousOn (fun u : ℝ => u⁻¹ + ((betaQ : ℝ) - u)⁻¹) (uIcc a b) := by
    apply ContinuousOn.add
    · apply ContinuousOn.inv₀ continuousOn_id
      intro u hu
      rw [uIcc_of_le hab] at hu
      change u ≠ 0
      linarith [hu.1]
    · apply ContinuousOn.inv₀ (by fun_prop)
      intro u hu
      rw [uIcc_of_le hab] at hu
      linarith [hu.2]
  have hm : MonotoneOn (fun u => u * ωp u) (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact (Ap_mono hω).mono (fun x hx => ha.trans hx.1)
  exact hm.intervalIntegrable.mul_continuousOn hc

/-- The cumulative certificate encloses the substituted integral before division by 2 beta. -/
theorem cumulative_bounds {ωp ωm : ℝ → ℝ} (hω : IsOmegaPair ωp ωm) :
    ∀ k, 156 ≤ k → k ≤ 359 →
    (FL k : ℝ) / 1000000000 ≤
      (∫ u in (xq 156 : ℝ)..(xq k : ℝ),
        (u * ωp u) * (u⁻¹ + ((betaQ : ℝ) - u)⁻¹)) ∧
    (∫ u in (xq 156 : ℝ)..(xq k : ℝ),
        (u * ωp u) * (u⁻¹ + ((betaQ : ℝ) - u)⁻¹)) ≤
      (FU k : ℝ) / 1000000000 := by
  intro k hkl
  induction k, hkl using Nat.le_induction with
  | base =>
    intro _
    norm_num [FL, FU, tFL, tFU]
  | succ k hkl ih =>
    intro hku
    have hprev := ih (by omega)
    have hstep := step_bounds hω k (by omega) hkl
    have cert := of_ball_split chk_F1 chk_F2 k hkl (by omega)
    simp only [chkF, decide_eq_true_eq] at cert
    have cl : (FL (k + 1) : ℝ) / 1000000000 ≤ (FL k : ℝ) / 1000000000 + (stepL k : ℝ) := by
      have h := (Rat.cast_le (K := ℝ)).mpr cert.1
      push_cast at h
      exact h
    have cu : (FU k : ℝ) / 1000000000 + (stepU k : ℝ) ≤ (FU (k + 1) : ℝ) / 1000000000 := by
      have h := (Rat.cast_le (K := ℝ)).mpr cert.2
      push_cast at h
      exact h
    have g := geometry k (by omega) hkl
    have ga : (1 : ℝ) < (xq k : ℝ) := by exact_mod_cast g.1
    have gab : (xq k : ℝ) ≤ (xq (k + 1) : ℝ) := by exact_mod_cast g.2.1
    have gbt : (xq (k + 1) : ℝ) < (betaQ : ℝ) := by exact_mod_cast g.2.2.1
    have gbase : (xq 156 : ℝ) ≤ (xq k : ℝ) := by
      by_cases heq : k = 156
      · subst k
        exact le_rfl
      · have hk157 : 157 ≤ k := by omega
        have hk358 : k ≤ 358 := by omega
        norm_num [xq, betaQ, show ¬ k ≤ 156 by omega, show ¬ 359 ≤ k by omega]
        have hkR : (157 : ℝ) ≤ k := by exact_mod_cast hk157
        linarith
    have hi0 := fint_integrable hω (a := (xq 156 : ℝ)) (b := (xq k : ℝ))
      (by norm_num [xq, betaQ]) gbase (by linarith)
    have hi1 := fint_integrable hω ga.le gab gbt
    have hsum := integral_add_adjacent_intervals hi0 hi1
    constructor <;> linarith [hprev.1, hprev.2, hstep.1, hstep.2]

/-- Printed page 31 enclosure for the page 36 substituted F integral. -/
theorem Fint_bounds {ωp ωm : ℝ → ℝ} (hω : IsOmegaPair ωp ωm) :
    (0.40941 : ℝ) ≤ fint ωp ∧ fint ωp ≤ 0.40943 := by
  have h := cumulative_bounds hω 359 (by norm_num) le_rfl
  have vals : FL 359 = 4484961612 ∧ FU 359 = 4485091347 := by decide +kernel
  rw [vals.1, vals.2] at h
  dsimp [fint]
  norm_num [betaQ] at h ⊢
  constructor <;> linarith [h.1, h.2]



/-- The certified integral is the page 36 formula with the combined reciprocal weight. -/
theorem fint_eq_substituted (ωp : ℝ → ℝ) :
    fint ωp = (1 / 2 : ℝ) *
      ∫ v in (21909 / 4000 - 67 / 19 : ℝ)..(17909 / 4000 : ℝ),
        (v * ωp v) / (v * (21909 / 4000 - v)) := by
  unfold fint
  norm_num [xq, betaQ]
  rw [← intervalIntegral.integral_div, ← intervalIntegral.integral_const_mul]
  apply integral_congr
  intro v hv
  rw [uIcc_of_le (by norm_num)] at hv
  have hv0 : v ≠ 0 := by linarith [hv.1]
  have hb0 : (21909 / 4000 : ℝ) - v ≠ 0 := by linarith [hv.2]
  have h3 : (21909 : ℝ) - v * 4000 ≠ 0 := by linarith [hv.2]
  field_simp [hv0, hb0, h3]
  ring

/-- The page 36 substitution identifies the certified value with the original Kuhn F integral. -/
theorem fint_eq_original (ωp : ℝ → ℝ) :
    fint ωp = (1 / 2 : ℝ) *
      ∫ u in (1 / 33.5 : ℝ)..(1 / 9.5 : ℝ), ωp (33.5 * (0.1635 - u)) / u := by
  let g : ℝ → ℝ := fun v => (v * ωp v) / (v * (21909 / 4000 - v))
  have hsub := integral_comp_sub_mul g (a := (1 / 33.5 : ℝ))
    (b := (1 / 9.5 : ℝ)) (c := (33.5 : ℝ)) (by norm_num) (21909 / 4000)
  have hcong : (∫ u in (1 / 33.5 : ℝ)..(1 / 9.5 : ℝ),
      ωp (33.5 * (0.1635 - u)) / u) =
      33.5 * ∫ u in (1 / 33.5 : ℝ)..(1 / 9.5 : ℝ), g (21909 / 4000 - 33.5 * u) := by
    rw [← intervalIntegral.integral_const_mul]
    apply integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num)] at hu
    have hu0 : u ≠ 0 := by linarith [hu.1]
    have hv0 : (21909 / 4000 : ℝ) - 33.5 * u ≠ 0 := by linarith [hu.2]
    have he : 33.5 * (0.1635 - u) = (21909 / 4000 : ℝ) - 33.5 * u := by ring
    dsimp only
    rw [he]
    dsimp [g]
    have hc : (21909 / 4000 : ℝ) - (21909 / 4000 - 33.5 * u) = 33.5 * u := by ring
    rw [hc, mul_div_mul_left _ _ hv0]
    field_simp [hu0]
  rw [fint_eq_substituted]
  change (1 / 2 : ℝ) * (∫ v in (21909 / 4000 - 67 / 19 : ℝ)..(17909 / 4000 : ℝ), g v) = _
  rw [hcong]
  norm_num only [smul_eq_mul] at hsub
  linarith

/-- Printed enclosure for the original page 36 Kuhn integral. -/
theorem Fint_original_bounds {ωp ωm : ℝ → ℝ} (hω : IsOmegaPair ωp ωm) :
    (0.40941 : ℝ) ≤ (1 / 2 : ℝ) *
      (∫ u in (1 / 33.5 : ℝ)..(1 / 9.5 : ℝ), ωp (33.5 * (0.1635 - u)) / u) ∧
    (1 / 2 : ℝ) *
      (∫ u in (1 / 33.5 : ℝ)..(1 / 9.5 : ℝ), ωp (33.5 * (0.1635 - u)) / u) ≤ 0.40943 := by
  rw [← fint_eq_original ωp]
  exact Fint_bounds hω

end LeanLab.Akeno2026.FIntegral
