import LeanLab.OpenProblems.Feed1122Novelty1615Split

/-!
# Erdős 273, Novelty1615: stacked split of `leaf_no_cover_bad`

AI wrote this Lean code. Erdős 273 is OPEN and so is binary Goldbach; nothing here touches either.
`Feed1122Split.leaf_no_cover_bad` rules out every candidate lcm in `badList`, 828 values below
`8000000`. This file reduces it, sorry free, to the 420 candidates in `[4000000, 8000000)`.
The reduction: if a covering `S` has lcm `L < 4000000` in `badList`, add one new congruence
`0 mod m`, with `m` from a fixed pool of twelve moduli `m = p - 1`, `p ≥ 5` prime, chosen so that
`m ∤ L` and `lcm L m` is again in `badList`. A superset of a covering is a covering, the modulus is
new because it does not divide `L`, and the lcm strictly grows, so induction ends in the upper
range. The pool and the finite table check were computed by session burst-20261122-S105 and are
checked here by `decide +kernel`.
-/

namespace LeanLab.OpenProblems.Novelty1615.Feed1122Stack

open LeanLab.OpenProblems.Erdos273 LeanLab.OpenProblems.Novelty1615
open LeanLab.OpenProblems.Novelty1615.Feed1122Split

/-- The pool of extension moduli, each `p - 1` with `p` prime: `p` runs over
`193, 97, 3457, 257, 641, 881, 15361, 7681, 12289, 18433, 40961, 41`. -/
def pool : List ℕ := [192, 96, 3456, 256, 640, 880, 15360, 7680, 12288, 18432, 40960, 40]

theorem pool_spec : ∀ m ∈ pool, (m + 1).Prime ∧ 4 ≤ m := by
  intro m hm
  simp only [pool, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by norm_num, by norm_num⟩

/-- Pieces of the extension witness table, a pair `(L, m)` with `m` in `pool` for each of the
408 candidates below `4000000`, computed by session burst-20261122-S105. -/
def wit0 : List (ℕ × ℕ) := [
  (55440, 192), (65520, 192), (100800, 3456), (110880, 192), (131040, 192), (151200, 192),
  (166320, 192), (181440, 3456), (196560, 192), (201600, 3456), (205920, 192), (221760, 3456),
  (226800, 192), (231840, 192), (241920, 880), (257040, 192), (262080, 3456), (277200, 192),
  (302400, 3456), (308880, 192), (327600, 192), (332640, 192), (342720, 3456), (347760, 192),
  (360360, 192), (362880, 256), (378000, 192), (388080, 192), (393120, 192), (403200, 3456),
  (411840, 3456), (415800, 192), (423360, 3456), (428400, 192), (438480, 192), (443520, 3456),
  (453600, 192), (458640, 192), (463680, 3456), (483840, 880), (498960, 192), (504000, 3456),
  (514080, 192), (514800, 192), (524160, 3456), (529200, 192), (544320, 3456), (554400, 192),
  (574560, 192), (579600, 192), (584640, 3456)]

def wit1 : List (ℕ × ℕ) := [
  (589680, 192), (604800, 256), (609840, 192), (617760, 192), (635040, 192), (637560, 192),
  (655200, 192), (665280, 3456), (680400, 192), (685440, 3456), (695520, 192), (705600, 3456),
  (720720, 192), (725760, 880), (730800, 192), (756000, 192), (771120, 192), (776160, 192),
  (786240, 3456), (806400, 3456), (811440, 192), (823680, 3456), (831600, 192), (846720, 256),
  (851760, 192), (856800, 192), (861840, 192), (876960, 192), (887040, 3456), (907200, 3456),
  (917280, 192), (926640, 192), (927360, 3456), (942480, 192), (957600, 192), (960960, 256),
  (967680, 12288), (982800, 192), (997920, 192), (1008000, 3456), (1028160, 3456), (1029600, 192),
  (1043280, 192), (1048320, 3456), (1053360, 192), (1058400, 192), (1081080, 96), (1088640, 256),
  (1092960, 192), (1108800, 3456), (1113840, 192)]

def wit2 : List (ℕ × ℕ) := [
  (1118880, 192), (1134000, 192), (1149120, 3456), (1159200, 192), (1164240, 192), (1169280, 3456),
  (1179360, 192), (1199520, 192), (1201200, 192), (1209600, 15360), (1219680, 192), (1235520, 3456),
  (1239840, 192), (1244880, 192), (1247400, 96), (1270080, 3456), (1275120, 192), (1285200, 192),
  (1310400, 3456), (1315440, 192), (1330560, 256), (1360800, 192), (1370880, 3456), (1375920, 192),
  (1386000, 192), (1391040, 3456), (1411200, 3456), (1413720, 96), (1425600, 3456), (1436400, 192),
  (1441440, 192), (1451520, 15360), (1461600, 192), (1496880, 192), (1506960, 192), (1512000, 3456),
  (1532160, 3456), (1542240, 192), (1544400, 192), (1552320, 256), (1562400, 192), (1572480, 256),
  (1580040, 96), (1587600, 192), (1602720, 192), (1607760, 192), (1612800, 3456), (1615680, 3456),
  (1622880, 192), (1627920, 192), (1632960, 3456)]

def wit3 : List (ℕ × ℕ) := [
  (1638000, 192), (1639440, 192), (1647360, 3456), (1663200, 192), (1678320, 192), (1693440, 15360),
  (1703520, 192), (1713600, 256), (1718640, 192), (1723680, 192), (1738800, 192), (1746360, 96),
  (1750320, 192), (1753920, 3456), (1764000, 192), (1769040, 192), (1774080, 3456), (1799280, 192),
  (1801800, 96), (1814400, 256), (1821600, 192), (1829520, 192), (1834560, 256), (1853280, 192),
  (1854720, 3456), (1859760, 192), (1864800, 192), (1874880, 3456), (1884960, 192), (1890000, 192),
  (1900080, 192), (1900800, 15360), (1905120, 192), (1912680, 96), (1915200, 256), (1921920, 256),
  (1935360, 12288), (1940400, 192), (1956240, 192), (1965600, 192), (1970640, 192), (1995840, 3456),
  (2010960, 96), (2016000, 3456), (2019600, 96), (2031120, 96), (2041200, 96), (2046240, 192),
  (2051280, 96), (2056320, 256), (2059200, 640)]

def wit4 : List (ℕ × ℕ) := [
  (2066400, 192), (2079000, 880), (2086560, 192), (2096640, 3456), (2106720, 192), (2116800, 3456),
  (2138400, 192), (2142000, 96), (2162160, 96), (2167200, 192), (2177280, 7680), (2185920, 3456),
  (2192400, 96), (2202480, 96), (2217600, 3456), (2227680, 192), (2237760, 3456), (2265120, 192),
  (2268000, 192), (2273040, 96), (2293200, 96), (2298240, 256), (2313360, 96), (2318400, 640),
  (2328480, 192), (2338560, 3456), (2343600, 96), (2356200, 880), (2358720, 3456), (2368080, 96),
  (2368800, 192), (2376000, 3456), (2383920, 96), (2394000, 96), (2399040, 640), (2402400, 192),
  (2411640, 880), (2419200, 15360), (2423520, 192), (2424240, 96), (2434320, 96), (2439360, 640),
  (2449440, 192), (2469600, 192), (2471040, 256), (2479680, 3456), (2484720, 96), (2489760, 192),
  (2494800, 96), (2520000, 640), (2522520, 880)]

def wit5 : List (ℕ × ℕ) := [
  (2540160, 256), (2550240, 192), (2555280, 96), (2570400, 192), (2574000, 96), (2585520, 96),
  (2600640, 3456), (2605680, 96), (2620800, 3456), (2630880, 192), (2633400, 880), (2646000, 96),
  (2661120, 7680), (2671200, 192), (2676960, 192), (2681280, 640), (2686320, 96), (2692800, 640),
  (2702700, 40), (2716560, 96), (2721600, 3456), (2732400, 96), (2741760, 15360), (2751840, 192),
  (2756160, 3456), (2772000, 192), (2779920, 96), (2782080, 256), (2797200, 96), (2812320, 192),
  (2817360, 96), (2822400, 7680), (2827440, 96), (2842560, 3456), (2851200, 256), (2872800, 192),
  (2882880, 640), (2898000, 96), (2903040, 18432), (2910600, 880), (2913120, 192), (2914560, 7680),
  (2923200, 640), (2938320, 96), (2948400, 96), (2963520, 3456), (2985840, 96), (2993760, 192),
  (2998800, 96), (3013920, 192), (3024000, 256)]

def wit6 : List (ℕ × ℕ) := [
  (3049200, 96), (3064320, 15360), (3069360, 96), (3079440, 96), (3084480, 3456), (3088800, 192),
  (3096720, 96), (3099600, 96), (3104640, 256), (3124800, 640), (3129840, 96), (3144960, 7680),
  (3160080, 96), (3170160, 96), (3175200, 192), (3187800, 880), (3205440, 3456), (3210480, 96),
  (3215520, 192), (3225600, 12288), (3231360, 256), (3243240, 880), (3245760, 640), (3250800, 96),
  (3255840, 192), (3265920, 256), (3270960, 96), (3276000, 192), (3278880, 192), (3294720, 15360),
  (3298680, 880), (3306240, 7680), (3326400, 3456), (3341520, 96), (3351600, 96), (3356640, 192),
  (3361680, 96), (3363360, 192), (3381840, 96), (3386880, 15360), (3397680, 96), (3402000, 96),
  (3407040, 640), (3409560, 880), (3427200, 256), (3437280, 192), (3445200, 96), (3447360, 3456),
  (3472560, 96), (3477600, 192), (3492720, 96)]

def wit7 : List (ℕ × ℕ) := [
  (3500640, 192), (3507840, 256), (3512880, 96), (3528000, 640), (3538080, 192), (3548160, 18432),
  (3553200, 96), (3564000, 192), (3568320, 3456), (3593520, 96), (3598560, 192), (3603600, 96),
  (3628800, 7680), (3643200, 640), (3654000, 96), (3659040, 192), (3669120, 256), (3684240, 96),
  (3689280, 3456), (3704400, 96), (3706560, 3456), (3709440, 15360), (3714480, 96), (3719520, 192),
  (3729600, 640), (3734640, 96), (3742200, 880), (3749760, 256), (3769920, 640), (3780000, 192),
  (3800160, 192), (3801600, 15360), (3809520, 96), (3810240, 3456), (3825360, 96), (3830400, 256),
  (3843840, 7680), (3855600, 96), (3865680, 96), (3870720, 40960), (3880800, 192), (3900960, 192),
  (3912480, 192), (3916080, 96), (3931200, 3456), (3936240, 96), (3941280, 192), (3946320, 96),
  (3963960, 880), (3991680, 256), (3996720, 96)]

/-- The full extension witness table. -/
def wit : List (ℕ × ℕ) := wit0 ++ wit1 ++ wit2 ++ wit3 ++ wit4 ++ wit5 ++ wit6 ++ wit7

/-- Boolean form of the witness check on a piece: each pair is a valid extension step. -/
def witOK (l : List (ℕ × ℕ)) : Bool :=
  l.all fun x => pool.contains x.2 && (x.1 % x.2 != 0) && badList.contains (Nat.lcm x.1 x.2) &&
    decide (x.1 < Nat.lcm x.1 x.2)

theorem witOK0 : witOK wit0 = true := by decide +kernel

theorem witOK1 : witOK wit1 = true := by decide +kernel

theorem witOK2 : witOK wit2 = true := by decide +kernel

theorem witOK3 : witOK wit3 = true := by decide +kernel

theorem witOK4 : witOK wit4 = true := by decide +kernel

theorem witOK5 : witOK wit5 = true := by decide +kernel

theorem witOK6 : witOK wit6 = true := by decide +kernel

theorem witOK7 : witOK wit7 = true := by decide +kernel

theorem witOK_append (l₁ l₂ : List (ℕ × ℕ)) : witOK (l₁ ++ l₂) = (witOK l₁ && witOK l₂) :=
  List.all_append

theorem witOK_true : witOK wit = true := by
  simp only [wit, witOK_append, witOK0, witOK1, witOK2, witOK3, witOK4, witOK5, witOK6, witOK7,
    Bool.and_self]

/-- The candidates below `4000000` are exactly the first coordinates of the witness table. -/
theorem low_eq : badList.filter (fun L => decide (L < 4000000)) = wit.map Prod.fst := by
  decide +kernel

theorem table : ∀ L ∈ badList, L < 4000000 →
    ∃ m ∈ pool, ¬ m ∣ L ∧ Nat.lcm L m ∈ badList ∧ L < Nat.lcm L m := by
  intro L hL hlt
  have h : L ∈ wit.map Prod.fst := by
    rw [← low_eq]
    simpa using ⟨hL, hlt⟩
  simp only [List.mem_map] at h
  obtain ⟨⟨L', m⟩, hx, rfl⟩ := h
  have hw := witOK_true
  simp only [witOK, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq,
    List.contains_iff_mem, decide_eq_true_eq] at hw
  obtain ⟨⟨⟨hm, hmod⟩, hmem⟩, hlt'⟩ := hw _ hx
  exact ⟨m, hm, fun hd => hmod (Nat.mod_eq_zero_of_dvd hd), hmem, hlt'⟩

/-- One extension step: adding `0 mod m` to a covering with a new modulus `m = p - 1`. -/
theorem extend (S : Finset (ℕ × ℤ)) (hS : Covers S) (hi : Set.InjOn Prod.fst (S : Set (ℕ × ℤ)))
    (hp : ∀ s ∈ S, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ s.1 = p - 1) (m : ℕ) (hmp : (m + 1).Prime)
    (hm4 : 4 ≤ m) (hnd : ¬ m ∣ S.lcm Prod.fst) :
    Covers (insert (m, (0 : ℤ)) S) ∧
      Set.InjOn Prod.fst ((insert (m, (0 : ℤ)) S : Finset (ℕ × ℤ)) : Set (ℕ × ℤ)) ∧
      (∀ s ∈ insert (m, (0 : ℤ)) S, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ s.1 = p - 1) ∧
      (insert (m, (0 : ℤ)) S).lcm Prod.fst = Nat.lcm (S.lcm Prod.fst) m := by
  have hnot : ∀ s ∈ S, s.1 ≠ m := by
    intro s hs h
    exact hnd (h ▸ Finset.dvd_lcm hs)
  have hnmem : (m, (0 : ℤ)) ∉ S := fun h => hnot _ h rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨s, hs, h⟩ := hS x
    exact ⟨s, Finset.mem_insert_of_mem hs, h⟩
  · rw [Finset.coe_insert, Set.injOn_insert (by simpa using hnmem)]
    refine ⟨hi, ?_⟩
    rintro ⟨s, hs, h⟩
    exact hnot s hs h
  · intro s hs
    rcases Finset.mem_insert.1 hs with rfl | hs
    · exact ⟨m + 1, hmp, by omega, by simp⟩
    · exact hp s hs
  · rw [Finset.lcm_insert, Nat.lcm_comm]
    rfl

/-- LEAF: residue search step of the cited search, https://github.com/veljjanoski/erdos273,
restricted to the upper block: no covering with distinct moduli `p - 1`, `p ≥ 5` prime, has its lcm
in `badList` and at least `4000000`. These are 420 of the 828 candidates. Implied by the cited
claim, no stronger than it. Class HARD: an exhaustive residue assignment search per candidate,
cited to the U-1615 search. -/
theorem leaf_no_cover_bad_high :
    ∀ S : Finset (ℕ × ℤ), Covers S → Set.InjOn Prod.fst (S : Set (ℕ × ℤ)) →
      (∀ s ∈ S, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ s.1 = p - 1) → S.lcm Prod.fst ∈ badList →
        4000000 ≤ S.lcm Prod.fst → False := by
  sorry

/-- Assembly, sorry free from the LEAF: the identical statement of
`Feed1122Split.leaf_no_cover_bad`. -/
theorem leaf_no_cover_bad_proved :
    ∀ S : Finset (ℕ × ℤ), Covers S → Set.InjOn Prod.fst (S : Set (ℕ × ℤ)) →
      (∀ s ∈ S, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ s.1 = p - 1) → S.lcm Prod.fst ∉ badList := by
  suffices H : ∀ n : ℕ, ∀ S : Finset (ℕ × ℤ), 8000000 - S.lcm Prod.fst = n → Covers S →
      Set.InjOn Prod.fst (S : Set (ℕ × ℤ)) →
      (∀ s ∈ S, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ s.1 = p - 1) → S.lcm Prod.fst ∉ badList from
    fun S => H _ S rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hn hS hi hp hb
    by_cases h4 : 4000000 ≤ S.lcm Prod.fst
    · exact leaf_no_cover_bad_high S hS hi hp hb h4
    push Not at h4
    obtain ⟨m, hm, hnd, hb', hlt⟩ := table _ hb h4
    obtain ⟨hmp, hm4⟩ := pool_spec m hm
    obtain ⟨hS', hi', hp', hl'⟩ := extend S hS hi hp m hmp hm4 hnd
    have hb8 : ∀ L ∈ badList, L < 8000000 := by decide +kernel
    have := hb8 _ hb'
    refine ih (8000000 - (insert (m, (0 : ℤ)) S).lcm Prod.fst) ?_ _ rfl hS' hi' hp' (hl' ▸ hb')
    rw [hl']
    omega

end LeanLab.OpenProblems.Novelty1615.Feed1122Stack
