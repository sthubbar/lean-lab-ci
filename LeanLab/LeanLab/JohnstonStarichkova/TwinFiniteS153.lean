/-
Johnston and Starichkova, P0019, arXiv 2208.01229v3, page 3, the twin prime constant C_2.
Burst S153 burst-20261122: certified finite product over the primes 50 < p at most 10^5, for the
LEAF twin_prime_tail_finite_ge of SPLIT_twin_prime_tail_ge.lean. Computed value 0.99604706500050810,
bound 0.996047. Async elaboration is off so the kernel chunks run one at a time, about 7.1 GB.
AI wrote this Lean code. Goldbach is open.
-/
import Mathlib

set_option Elab.async false

namespace LeanLab.JohnstonStarichkova
open Finset

/-- Trial division by every d below 317, enough for n up to 10^5: true iff n has no divisor d
with 2 ≤ d < n and d < 317. Helper for the certified finite product of P0019 v3 page 3. -/
def twinTrialOK (n : ℕ) : Bool := (List.range 317).all (fun d => d < 2 || n ≤ d || n % d != 0)

/-- One step of the rounded down product: at n = k + 1 passing trial division, multiply the
fixed point accumulator by 1 - 1/k^2 and round down. Helper, P0019 v3 page 3. -/
def twinStep (k acc : ℕ) : ℕ := if twinTrialOK (k + 1) then acc * (k ^ 2 - 1) / k ^ 2 else acc

/-- Iterated rounded down product over n = a + 1 to a + len. Helper, P0019 v3 page 3. -/
def twinIter : ℕ → ℕ → ℕ → ℕ
  | _, 0, acc => acc
  | a, len + 1, acc => twinIter (a + 1) len (twinStep a acc)

theorem twin_factor_nonneg_S153 (x : ℝ) (hx : 3 ≤ x) : 0 ≤ 1 - 1 / (x - 1) ^ 2 := by
  rw [sub_nonneg, div_le_one (by nlinarith)]; nlinarith

theorem twinIter_add_S153 (l1 l2 : ℕ) : ∀ a acc, twinIter a (l1 + l2) acc = twinIter (a + l1) l2 (twinIter a l1 acc) := by
  induction l1 with
  | zero => intro a acc; simp [twinIter]
  | succ l ih =>
    intro a acc
    rw [show l + 1 + l2 = (l + l2) + 1 by ring, twinIter, ih, twinIter]
    congr 1; ring

theorem prime_twinTrialOK_S153 {n : ℕ} (hn : n.Prime) : twinTrialOK n = true := by
  unfold twinTrialOK
  rw [List.all_eq_true]
  intro d _
  by_contra h
  simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, not_or, not_lt, not_le,
    not_not] at h
  obtain ⟨⟨h2, hlt⟩, hmod⟩ := h
  rcases hn.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero hmod) with h | h <;> omega

theorem twinStep_le_S153 (k acc : ℕ) (hk : 2 ≤ k) :
    (twinStep k acc : ℝ) ≤ acc * (if twinTrialOK (k + 1) then 1 - 1 / (((k + 1 : ℕ) : ℝ) - 1) ^ 2 else 1) := by
  unfold twinStep
  by_cases ht : twinTrialOK (k + 1) = true
  · rw [if_pos ht, if_pos ht]
    have hk2 : 1 ≤ k ^ 2 := Nat.one_le_pow _ _ (by omega)
    calc ((acc * (k ^ 2 - 1) / k ^ 2 : ℕ) : ℝ) ≤ ((acc * (k ^ 2 - 1) : ℕ) : ℝ) / ((k ^ 2 : ℕ) : ℝ) :=
          Nat.cast_div_le
      _ = acc * (1 - 1 / (((k + 1 : ℕ) : ℝ) - 1) ^ 2) := by
          have hk0 : (k : ℝ) ≠ 0 := by have : (2 : ℝ) ≤ k := by exact_mod_cast hk
                                       linarith
          rw [show (((k + 1 : ℕ) : ℝ) - 1) = k by push_cast; ring, Nat.cast_mul, Nat.cast_sub hk2]
          push_cast
          field_simp
  · rw [if_neg ht, if_neg ht, mul_one]

theorem twinIter_le_S153 (len : ℕ) : ∀ a acc, 2 ≤ a →
    (twinIter a len acc : ℝ) ≤ acc * ∏ n ∈ Ioc a (a + len),
      (if twinTrialOK n then 1 - 1 / ((n : ℝ) - 1) ^ 2 else 1) := by
  induction len with
  | zero => intro a acc _; simp [twinIter]
  | succ l ih =>
    intro a acc ha
    rw [twinIter]
    have hsplit : ∏ n ∈ Ioc a (a + (l + 1)), (if twinTrialOK n then 1 - 1 / ((n : ℝ) - 1) ^ 2 else 1) =
        (if twinTrialOK (a + 1) then 1 - 1 / (((a + 1 : ℕ) : ℝ) - 1) ^ 2 else 1) *
        ∏ n ∈ Ioc (a + 1) (a + 1 + l), (if twinTrialOK n then 1 - 1 / ((n : ℝ) - 1) ^ 2 else 1) := by
      rw [← prod_Ioc_consecutive _ (show a ≤ a + 1 by omega) (show a + 1 ≤ a + (l + 1) by omega),
        Nat.Ioc_succ_singleton, prod_singleton, show a + (l + 1) = a + 1 + l by ring]
    have hP : 0 ≤ ∏ n ∈ Ioc (a + 1) (a + 1 + l), (if twinTrialOK n then 1 - 1 / ((n : ℝ) - 1) ^ 2 else 1) := by
      apply prod_nonneg
      intro n hn
      have hn2 : (3 : ℝ) ≤ n := by
        have := (mem_Ioc.mp hn).1; exact_mod_cast (show 3 ≤ n by omega)
      by_cases ht : twinTrialOK n = true
      · rw [if_pos ht]; exact twin_factor_nonneg_S153 _ (by linarith)
      · rw [if_neg ht]; norm_num
    have h1 := ih (a + 1) (twinStep a acc) (by omega)
    have h2 := twinStep_le_S153 a acc ha
    rw [hsplit]
    calc (twinIter (a + 1) l (twinStep a acc) : ℝ) ≤ twinStep a acc * _ := h1
      _ ≤ (acc * (if twinTrialOK (a + 1) then 1 - 1 / (((a + 1 : ℕ) : ℝ) - 1) ^ 2 else 1)) * _ :=
          mul_le_mul_of_nonneg_right h2 hP
      _ = _ := by ring

theorem twinChunk_0_S153 : twinIter 50 1000 1000000000000000000000000000000 = 996165318165746212537852083283 := by decide +kernel
theorem twinChunk_1_S153 : twinIter 1050 1000 996165318165746212537852083283 = 996102916792037402321249237920 := by decide +kernel
theorem twinChunk_2_S153 : twinIter 2050 1000 996102916792037402321249237920 = 996082434598636720308867609345 := by decide +kernel
theorem twinChunk_3_S153 : twinIter 3050 1000 996082434598636720308867609345 = 996072733210151772835775549684 := by decide +kernel
theorem twinChunk_4_S153 : twinIter 4050 1000 996072733210151772835775549684 = 996067035554787775366213628112 := by decide +kernel
theorem twinChunk_5_S153 : twinIter 5050 1000 996067035554787775366213628112 = 996063318620619146772881639165 := by decide +kernel
theorem twinChunk_6_S153 : twinIter 6050 1000 996063318620619146772881639165 = 996060587272333622790442012860 := by decide +kernel
theorem twinChunk_7_S153 : twinIter 7050 1000 996060587272333622790442012860 = 996058746116221942209798550978 := by decide +kernel
theorem twinChunk_8_S153 : twinIter 8050 1000 996058746116221942209798550978 = 996057188945706569411789282269 := by decide +kernel
theorem twinChunk_9_S153 : twinIter 9050 1000 996057188945706569411789282269 = 996056004206997702993395270589 := by decide +kernel
theorem twinChunk_10_S153 : twinIter 10050 1000 996056004206997702993395270589 = 996055057856559676156175175439 := by decide +kernel
theorem twinChunk_11_S153 : twinIter 11050 1000 996055057856559676156175175439 = 996054265502556345113949416617 := by decide +kernel
theorem twinChunk_12_S153 : twinIter 12050 1000 996054265502556345113949416617 = 996053564035737498578064085909 := by decide +kernel
theorem twinChunk_13_S153 : twinIter 13050 1000 996053564035737498578064085909 = 996053015917835481173678332449 := by decide +kernel
theorem twinChunk_14_S153 : twinIter 14050 1000 996053015917835481173678332449 = 996052540666972881417118116281 := by decide +kernel
theorem twinChunk_15_S153 : twinIter 15050 1000 996052540666972881417118116281 = 996052093758461003824058668676 := by decide +kernel
theorem twinChunk_16_S153 : twinIter 16050 1000 996052093758461003824058668676 = 996051722485110286232244245319 := by decide +kernel
theorem twinChunk_17_S153 : twinIter 17050 1000 996051722485110286232244245319 = 996051392920109588504648797158 := by decide +kernel
theorem twinChunk_18_S153 : twinIter 18050 1000 996051392920109588504648797158 = 996051119438369011626287021880 := by decide +kernel
theorem twinChunk_19_S153 : twinIter 19050 1000 996051119438369011626287021880 = 996050848362728432745603250057 := by decide +kernel
theorem twinChunk_20_S153 : twinIter 20050 1000 996050848362728432745603250057 = 996050612233511191376901486770 := by decide +kernel
theorem twinChunk_21_S153 : twinIter 21050 1000 996050612233511191376901486770 = 996050391214259219308115646296 := by decide +kernel
theorem twinChunk_22_S153 : twinIter 22050 1000 996050391214259219308115646296 = 996050191264486472381991114849 := by decide +kernel
theorem twinChunk_23_S153 : twinIter 23050 1000 996050191264486472381991114849 = 996050006422538640629798939342 := by decide +kernel
theorem twinChunk_24_S153 : twinIter 24050 1000 996050006422538640629798939342 = 996049855798039500987970594290 := by decide +kernel
theorem twinChunk_25_S153 : twinIter 25050 1000 996049855798039500987970594290 = 996049704758850963984582915712 := by decide +kernel
theorem twinChunk_26_S153 : twinIter 26050 1000 996049704758850963984582915712 = 996049563467062292057726150986 := by decide +kernel
theorem twinChunk_27_S153 : twinIter 27050 1000 996049563467062292057726150986 = 996049440221208664462109919340 := by decide +kernel
theorem twinChunk_28_S153 : twinIter 28050 1000 996049440221208664462109919340 = 996049318025998364272997291167 := by decide +kernel
theorem twinChunk_29_S153 : twinIter 29050 1000 996049318025998364272997291167 = 996049215162205063073874462381 := by decide +kernel
theorem twinChunk_30_S153 : twinIter 30050 1000 996049215162205063073874462381 = 996049113662581022758378024205 := by decide +kernel
theorem twinChunk_31_S153 : twinIter 31050 1000 996049113662581022758378024205 = 996049021316804723358055740763 := by decide +kernel
theorem twinChunk_32_S153 : twinIter 32050 1000 996049021316804723358055740763 = 996048920603882314078930953100 := by decide +kernel
theorem twinChunk_33_S153 : twinIter 33050 1000 996048920603882314078930953100 = 996048832962761140162149275949 := by decide +kernel
theorem twinChunk_34_S153 : twinIter 34050 1000 996048832962761140162149275949 = 996048756101002772301026622682 := by decide +kernel
theorem twinChunk_35_S153 : twinIter 35050 1000 996048756101002772301026622682 = 996048681151289203622216297477 := by decide +kernel
theorem twinChunk_36_S153 : twinIter 36050 1000 996048681151289203622216297477 = 996048606673464266987789610476 := by decide +kernel
theorem twinChunk_37_S153 : twinIter 37050 1000 996048606673464266987789610476 = 996048542375275842347781629529 := by decide +kernel
theorem twinChunk_38_S153 : twinIter 38050 1000 996048542375275842347781629529 = 996048480762731608301221498843 := by decide +kernel
theorem twinChunk_39_S153 : twinIter 39050 1000 996048480762731608301221498843 = 996048419616948677197628486260 := by decide +kernel
theorem twinChunk_40_S153 : twinIter 40050 1000 996048419616948677197628486260 = 996048366334776310070081462336 := by decide +kernel
theorem twinChunk_41_S153 : twinIter 41050 1000 996048366334776310070081462336 = 996048308067892807190222992467 := by decide +kernel
theorem twinChunk_42_S153 : twinIter 42050 1000 996048308067892807190222992467 = 996048251935934458990203810873 := by decide +kernel
theorem twinChunk_43_S153 : twinIter 43050 1000 996048251935934458990203810873 = 996048207345150958185388768428 := by decide +kernel
theorem twinChunk_44_S153 : twinIter 44050 1000 996048207345150958185388768428 = 996048160636303242088773753577 := by decide +kernel
theorem twinChunk_45_S153 : twinIter 45050 1000 996048160636303242088773753577 = 996048118840528460494609949333 := by decide +kernel
theorem twinChunk_46_S153 : twinIter 46050 1000 996048118840528460494609949333 = 996048077877862354272077457851 := by decide +kernel
theorem twinChunk_47_S153 : twinIter 47050 1000 996048077877862354272077457851 = 996048035132857908883798229440 := by decide +kernel
theorem twinChunk_48_S153 : twinIter 48050 1000 996048035132857908883798229440 = 996047996286275575388506856350 := by decide +kernel
theorem twinChunk_49_S153 : twinIter 49050 1000 996047996286275575388506856350 = 996047957736609575498929098039 := by decide +kernel
theorem twinChunk_50_S153 : twinIter 50050 1000 996047957736609575498929098039 = 996047923010731751530547624499 := by decide +kernel
theorem twinChunk_51_S153 : twinIter 51050 1000 996047923010731751530547624499 = 996047887019701242138611054600 := by decide +kernel
theorem twinChunk_52_S153 : twinIter 52050 1000 996047887019701242138611054600 = 996047854911486939634172203957 := by decide +kernel
theorem twinChunk_53_S153 : twinIter 53050 1000 996047854911486939634172203957 = 996047822251132667584099551420 := by decide +kernel
theorem twinChunk_54_S153 : twinIter 54050 1000 996047822251132667584099551420 = 996047792459061983381695597744 := by decide +kernel
theorem twinChunk_55_S153 : twinIter 55050 1000 996047792459061983381695597744 = 996047762449981296410406496719 := by decide +kernel
theorem twinChunk_56_S153 : twinIter 56050 1000 996047762449981296410406496719 = 996047731940179399631772356410 := by decide +kernel
theorem twinChunk_57_S153 : twinIter 57050 1000 996047731940179399631772356410 = 996047703962611431501789391618 := by decide +kernel
theorem twinChunk_58_S153 : twinIter 58050 1000 996047703962611431501789391618 = 996047677795625203465139619084 := by decide +kernel
theorem twinChunk_59_S153 : twinIter 59050 1000 996047677795625203465139619084 = 996047651357628011083741826672 := by decide +kernel
theorem twinChunk_60_S153 : twinIter 60050 1000 996047651357628011083741826672 = 996047627450626539139338240660 := by decide +kernel
theorem twinChunk_61_S153 : twinIter 61050 1000 996047627450626539139338240660 = 996047604589539547519059448110 := by decide +kernel
theorem twinChunk_62_S153 : twinIter 62050 1000 996047604589539547519059448110 = 996047582943535482135697195560 := by decide +kernel
theorem twinChunk_63_S153 : twinIter 63050 1000 996047582943535482135697195560 = 996047559264985877959090484422 := by decide +kernel
theorem twinChunk_64_S153 : twinIter 64050 1000 996047559264985877959090484422 = 996047540145819808541131094036 := by decide +kernel
theorem twinChunk_65_S153 : twinIter 65050 1000 996047540145819808541131094036 = 996047517653538894894474174037 := by decide +kernel
theorem twinChunk_66_S153 : twinIter 66050 1000 996047517653538894894474174037 = 996047498549241986629555832556 := by decide +kernel
theorem twinChunk_67_S153 : twinIter 67050 1000 996047498549241986629555832556 = 996047477587385407725564554158 := by decide +kernel
theorem twinChunk_68_S153 : twinIter 68050 1000 996047477587385407725564554158 = 996047459999640899566684353906 := by decide +kernel
theorem twinChunk_69_S153 : twinIter 69050 1000 996047459999640899566684353906 = 996047443316288016242331673645 := by decide +kernel
theorem twinChunk_70_S153 : twinIter 70050 1000 996047443316288016242331673645 = 996047424098916189219031705133 := by decide +kernel
theorem twinChunk_71_S153 : twinIter 71050 1000 996047424098916189219031705133 = 996047405422116900408373630542 := by decide +kernel
theorem twinChunk_72_S153 : twinIter 72050 1000 996047405422116900408373630542 = 996047388019283313464230302181 := by decide +kernel
theorem twinChunk_73_S153 : twinIter 73050 1000 996047388019283313464230302181 = 996047373111659044277798216729 := by decide +kernel
theorem twinChunk_74_S153 : twinIter 74050 1000 996047373111659044277798216729 = 996047356261372314626989232071 := by decide +kernel
theorem twinChunk_75_S153 : twinIter 75050 1000 996047356261372314626989232071 = 996047340733599808657414528172 := by decide +kernel
theorem twinChunk_76_S153 : twinIter 76050 1000 996047340733599808657414528172 = 996047326288890375479028649058 := by decide +kernel
theorem twinChunk_77_S153 : twinIter 77050 1000 996047326288890375479028649058 = 996047310721719322850028241331 := by decide +kernel
theorem twinChunk_78_S153 : twinIter 78050 1000 996047310721719322850028241331 = 996047297484028303176232831589 := by decide +kernel
theorem twinChunk_79_S153 : twinIter 79050 1000 996047297484028303176232831589 = 996047283319156029604961267853 := by decide +kernel
theorem twinChunk_80_S153 : twinIter 80050 1000 996047283319156029604961267853 = 996047268591264313729837719432 := by decide +kernel
theorem twinChunk_81_S153 : twinIter 81050 1000 996047268591264313729837719432 = 996047255120504399184092424943 := by decide +kernel
theorem twinChunk_82_S153 : twinIter 82050 1000 996047255120504399184092424943 = 996047242691521677106998860765 := by decide +kernel
theorem twinChunk_83_S153 : twinIter 83050 1000 996047242691521677106998860765 = 996047230840928865666504391370 := by decide +kernel
theorem twinChunk_84_S153 : twinIter 84050 1000 996047230840928865666504391370 = 996047218434026512028654160443 := by decide +kernel
theorem twinChunk_85_S153 : twinIter 85050 1000 996047218434026512028654160443 = 996047206995801702158319759732 := by decide +kernel
theorem twinChunk_86_S153 : twinIter 86050 1000 996047206995801702158319759732 = 996047195155007468499941390009 := by decide +kernel
theorem twinChunk_87_S153 : twinIter 87050 1000 996047195155007468499941390009 = 996047183072676326621569270885 := by decide +kernel
theorem twinChunk_88_S153 : twinIter 88050 1000 996047183072676326621569270885 = 996047173430030645091198275451 := by decide +kernel
theorem twinChunk_89_S153 : twinIter 89050 1000 996047173430030645091198275451 = 996047161506738911093759042962 := by decide +kernel
theorem twinChunk_90_S153 : twinIter 90050 1000 996047161506738911093759042962 = 996047151175019919106445952205 := by decide +kernel
theorem twinChunk_91_S153 : twinIter 91050 1000 996047151175019919106445952205 = 996047140950884116893786600609 := by decide +kernel
theorem twinChunk_92_S153 : twinIter 92050 1000 996047140950884116893786600609 = 996047129901502357226554078788 := by decide +kernel
theorem twinChunk_93_S153 : twinIter 93050 1000 996047129901502357226554078788 = 996047119881870435328265034541 := by decide +kernel
theorem twinChunk_94_S153 : twinIter 94050 1000 996047119881870435328265034541 = 996047110187569616558755606841 := by decide +kernel
theorem twinChunk_95_S153 : twinIter 95050 1000 996047110187569616558755606841 = 996047099819616731748842402320 := by decide +kernel
theorem twinChunk_96_S153 : twinIter 96050 1000 996047099819616731748842402320 = 996047090739880869872808281787 := by decide +kernel
theorem twinChunk_97_S153 : twinIter 97050 1000 996047090739880869872808281787 = 996047082160271710846499848471 := by decide +kernel
theorem twinChunk_98_S153 : twinIter 98050 1000 996047082160271710846499848471 = 996047073347254303590257042910 := by decide +kernel
theorem twinChunk_99_S153 : twinIter 99050 950 996047073347254303590257042910 = 996047065000508103061840138266 := by decide +kernel


set_option maxRecDepth 20000 in
/-- The finite part of the tail of C_2, P0019 v3 page 3: the product over primes 50 < p at most
10^5 of 1 - 1/(p-1)^2 is at least 0.996047. Trial division keeps every prime, so the product
over the trial survivors is at most the prime product; the survivors product is bounded below by a
rounded down fixed point product at scale 10^30, checked in 100 kernel chunks of 1000 steps. -/
theorem twin_prime_tail_finite_ge_S153 :
    (996047 / 1000000 : ℝ) ≤ ∏ p ∈ (Finset.Ioc 50 100000).filter Nat.Prime,
      (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  have hit : twinIter 50 99950 (10 ^ 30) = 996047065000508103061840138266 := by
    have e : (99950 : ℕ) = 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 1000 + 950 := by norm_num
    rw [e]
    simp only [twinIter_add_S153]
    norm_num only [twinChunk_0_S153, twinChunk_1_S153, twinChunk_2_S153, twinChunk_3_S153, twinChunk_4_S153, twinChunk_5_S153, twinChunk_6_S153, twinChunk_7_S153, twinChunk_8_S153, twinChunk_9_S153, twinChunk_10_S153, twinChunk_11_S153, twinChunk_12_S153, twinChunk_13_S153, twinChunk_14_S153, twinChunk_15_S153, twinChunk_16_S153, twinChunk_17_S153, twinChunk_18_S153, twinChunk_19_S153, twinChunk_20_S153, twinChunk_21_S153, twinChunk_22_S153, twinChunk_23_S153, twinChunk_24_S153, twinChunk_25_S153, twinChunk_26_S153, twinChunk_27_S153, twinChunk_28_S153, twinChunk_29_S153, twinChunk_30_S153, twinChunk_31_S153, twinChunk_32_S153, twinChunk_33_S153, twinChunk_34_S153, twinChunk_35_S153, twinChunk_36_S153, twinChunk_37_S153, twinChunk_38_S153, twinChunk_39_S153, twinChunk_40_S153, twinChunk_41_S153, twinChunk_42_S153, twinChunk_43_S153, twinChunk_44_S153, twinChunk_45_S153, twinChunk_46_S153, twinChunk_47_S153, twinChunk_48_S153, twinChunk_49_S153, twinChunk_50_S153, twinChunk_51_S153, twinChunk_52_S153, twinChunk_53_S153, twinChunk_54_S153, twinChunk_55_S153, twinChunk_56_S153, twinChunk_57_S153, twinChunk_58_S153, twinChunk_59_S153, twinChunk_60_S153, twinChunk_61_S153, twinChunk_62_S153, twinChunk_63_S153, twinChunk_64_S153, twinChunk_65_S153, twinChunk_66_S153, twinChunk_67_S153, twinChunk_68_S153, twinChunk_69_S153, twinChunk_70_S153, twinChunk_71_S153, twinChunk_72_S153, twinChunk_73_S153, twinChunk_74_S153, twinChunk_75_S153, twinChunk_76_S153, twinChunk_77_S153, twinChunk_78_S153, twinChunk_79_S153, twinChunk_80_S153, twinChunk_81_S153, twinChunk_82_S153, twinChunk_83_S153, twinChunk_84_S153, twinChunk_85_S153, twinChunk_86_S153, twinChunk_87_S153, twinChunk_88_S153, twinChunk_89_S153, twinChunk_90_S153, twinChunk_91_S153, twinChunk_92_S153, twinChunk_93_S153, twinChunk_94_S153, twinChunk_95_S153, twinChunk_96_S153, twinChunk_97_S153, twinChunk_98_S153, twinChunk_99_S153]
  have hle := twinIter_le_S153 99950 50 (10 ^ 30) (by norm_num)
  rw [hit] at hle
  have hge : ∏ n ∈ Ioc 50 (50 + 99950), (if twinTrialOK n then 1 - 1 / ((n : ℝ) - 1) ^ 2 else 1) ≤
      ∏ p ∈ (Finset.Ioc 50 100000).filter Nat.Prime, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
    rw [prod_filter, show 50 + 99950 = 100000 by norm_num]
    refine Finset.prod_le_prod₀ ?_ ?_
    · intro n hn
      have hn2 : (51 : ℝ) ≤ n := by exact_mod_cast (mem_Ioc.mp hn).1
      clear hn
      by_cases ht : twinTrialOK n = true
      · rw [if_pos ht]; exact twin_factor_nonneg_S153 _ (by linarith)
      · rw [if_neg ht]; norm_num
    · intro n hn
      clear hn
      by_cases hp : n.Prime
      · rw [if_pos (prime_twinTrialOK_S153 hp), if_pos hp]
      · rw [if_neg hp]
        by_cases ht : twinTrialOK n = true
        · rw [if_pos ht]
          have : 0 ≤ 1 / ((n : ℝ) - 1) ^ 2 := by positivity
          linarith
        · rw [if_neg ht]
  have : (996047 / 1000000 : ℝ) * 10 ^ 30 ≤ (996047065000508103061840138266 : ℕ) := by norm_num
  push_cast at hle this
  linarith

end LeanLab.JohnstonStarichkova
