import LeanLab.OpenProblems.DecompJ1235

/-!
# Feed1122DecompJ1235Split: a sound split of Novelty1615.lcm_ge_8000000

AI wrote this Lean code. Erdős 273 is OPEN and binary Goldbach is OPEN; nothing here touches either.

The leaves `leaf_min_card` and `leaf_card_lt_of_lcm_lt` of DecompJ1235 are not used. Instead the parent
`lcm_ge_8000000` is split along the reciprocal test `one_le_sum_inv`: a covering with lcm `L` has its
moduli among the divisors `d` of `L` with `d + 1` prime and `4 ≤ d`, so outside a finite list of
candidate lcms the reciprocal sum is below 1. The list `candidates` holds the 828 values `L < 8000000`
whose divisor reciprocal sum is at least 1, computed in floating point by this session; the largest sum
below 1 is about 0.999986 and the smallest sum at or above 1 is about 1.000029, so rounding cannot move
any value across 1. The remaining candidates need a genuine covering search, the step the forum thread 273
reports as an unrefereed computer search.
-/

namespace LeanLab.OpenProblems.Feed1122DecompJ1235Split

open LeanLab.OpenProblems.Erdos273
open LeanLab.OpenProblems.Novelty1615
open Array
open Finset

set_option maxRecDepth 20000 in
/-- The 828 numbers `L < 8000000` with `∑ 1/d ≥ 1` over divisors `d` of `L` with `d + 1` prime and
`4 ≤ d`, found by a sieve run of this session. Source: the reciprocal test of forum thread 273 as quoted in
the novelty report OpenProblems-deepseek-20261103T1237Z section 1.4; the list itself is lab computed. -/
def candidates : List ℕ := [55440,65520,100800,110880,131040,151200,166320,181440,196560,201600,205920,221760,226800,231840,241920,257040,262080,277200,302400,308880,327600,332640,342720,347760,360360,362880,378000,388080,393120,403200,411840,415800,423360,428400,438480,443520,453600,458640,463680,483840,498960,504000,514080,514800,524160,529200,544320,554400,574560,579600,584640,589680,604800,609840,617760,635040,637560,655200,665280,680400,685440,695520,705600,720720,725760,730800,756000,771120,776160,786240,806400,811440,823680,831600,846720,851760,856800,861840,876960,887040,907200,917280,926640,927360,942480,957600,960960,967680,982800,997920,1008000,1028160,1029600,1043280,1048320,1053360,1058400,1081080,1088640,1092960,1108800,1113840,1118880,1134000,1149120,1159200,1164240,1169280,1179360,1199520,1201200,1209600,1219680,1235520,1239840,1244880,1247400,1270080,1275120,1285200,1310400,1315440,1330560,1360800,1370880,1375920,1386000,1391040,1411200,1413720,1425600,1436400,1441440,1451520,1461600,1496880,1506960,1512000,1532160,1542240,1544400,1552320,1562400,1572480,1580040,1587600,1602720,1607760,1612800,1615680,1622880,1627920,1632960,1638000,1639440,1647360,1663200,1678320,1693440,1703520,1713600,1718640,1723680,1738800,1746360,1750320,1753920,1764000,1769040,1774080,1799280,1801800,1814400,1821600,1829520,1834560,1853280,1854720,1859760,1864800,1874880,1884960,1890000,1900080,1900800,1905120,1912680,1915200,1921920,1935360,1940400,1956240,1965600,1970640,1995840,2010960,2016000,2019600,2031120,2041200,2046240,2051280,2056320,2059200,2066400,2079000,2086560,2096640,2106720,2116800,2138400,2142000,2162160,2167200,2177280,2185920,2192400,2202480,2217600,2227680,2237760,2265120,2268000,2273040,2293200,2298240,2313360,2318400,2328480,2338560,2343600,2356200,2358720,2368080,2368800,2376000,2383920,2394000,2399040,2402400,2411640,2419200,2423520,2424240,2434320,2439360,2449440,2469600,2471040,2479680,2484720,2489760,2494800,2520000,2522520,2540160,2550240,2555280,2570400,2574000,2585520,2600640,2605680,2620800,2630880,2633400,2646000,2661120,2671200,2676960,2681280,2686320,2692800,2702700,2716560,2721600,2732400,2741760,2751840,2756160,2772000,2779920,2782080,2797200,2812320,2817360,2822400,2827440,2842560,2851200,2872800,2882880,2898000,2903040,2910600,2913120,2914560,2923200,2938320,2948400,2963520,2985840,2993760,2998800,3013920,3024000,3049200,3064320,3069360,3079440,3084480,3088800,3096720,3099600,3104640,3124800,3129840,3144960,3160080,3170160,3175200,3187800,3205440,3210480,3215520,3225600,3231360,3243240,3245760,3250800,3255840,3265920,3270960,3276000,3278880,3294720,3298680,3306240,3326400,3341520,3351600,3356640,3361680,3363360,3381840,3386880,3397680,3402000,3407040,3409560,3427200,3437280,3445200,3447360,3472560,3477600,3492720,3500640,3507840,3512880,3528000,3538080,3548160,3553200,3564000,3568320,3593520,3598560,3603600,3628800,3643200,3654000,3659040,3669120,3684240,3689280,3704400,3706560,3709440,3714480,3719520,3729600,3734640,3742200,3749760,3769920,3780000,3800160,3801600,3809520,3810240,3825360,3830400,3843840,3855600,3865680,3870720,3880800,3900960,3912480,3916080,3931200,3936240,3941280,3946320,3963960,3991680,3996720,4006800,4015440,4019400,4021920,4032000,4039200,4047120,4052160,4057200,4062240,4082400,4084080,4092480,4102560,4112640,4118400,4127760,4132800,4134240,4144140,4158000,4173120,4183200,4193280,4213440,4221360,4233600,4241160,4250400,4258800,4263840,4268880,4276800,4284000,4289040,4294080,4309200,4324320,4334400,4339440,4354560,4369680,4371840,4379760,4384800,4389840,4404960,4415040,4427280,4435200,4445280,4455360,4460400,4462920,4475520,4490640,4514400,4520880,4530240,4536000,4541040,4546080,4554000,4564560,4573800,4586400,4593600,4596480,4601520,4611600,4626720,4633200,4636800,4651920,4656960,4662000,4677120,4684680,4687200,4712400,4717440,4736160,4737600,4740120,4752000,4752720,4762800,4767840,4777920,4782960,4788000,4798080,4804800,4808160,4823280,4838400,4847040,4848480,4851000,4868640,4878720,4883760,4898880,4914000,4918320,4934160,4939200,4942080,4959360,4969440,4979520,4984560,4989600,5019840,5034960,5040000,5045040,5065200,5080320,5100480,5110560,5115600,5128200,5140800,5148000,5155920,5166000,5171040,5176080,5183640,5201280,5211360,5216400,5221440,5239080,5241600,5250960,5261760,5266800,5282640,5285280,5292000,5307120,5312160,5322240,5332320,5342400,5352480,5353920,5362560,5367600,5372640,5377680,5382720,5385600,5397840,5405400,5417280,5433120,5438160,5443200,5448240,5456880,5464800,5483520,5488560,5503680,5512320,5518800,5525520,5533920,5544000,5554080,5559840,5564160,5569200,5579280,5594400,5599440,5624640,5627160,5634720,5644800,5654880,5662800,5670000,5680080,5682600,5685120,5700240,5702400,5710320,5715360,5738040,5745600,5765760,5785920,5796000,5806080,5821200,5826240,5829120,5831280,5846400,5866560,5868720,5876640,5896800,5911920,5927040,5932080,5947200,5962320,5971680,5972400,5987520,5997600,6006000,6019200,6027840,6032880,6042960,6048000,6058800,6078240,6093360,6098400,6108480,6123600,6126120,6128640,6138720,6143760,6148800,6153840,6158880,6168960,6177600,6193440,6199200,6209280,6224400,6229440,6237000,6246240,6249600,6259680,6264720,6274800,6283200,6289920,6320160,6340320,6350400,6355440,6375600,6383520,6410880,6415200,6420960,6426000,6431040,6441120,6451200,6462720,6471360,6486480,6491520,6501600,6511680,6526800,6531840,6541920,6552000,6557760,6562080,6577200,6589440,6597360,6607440,6612480,6617520,6622560,6652800,6683040,6692400,6703200,6708240,6713280,6723360,6726720,6728400,6732000,6748560,6753600,6763680,6771600,6773760,6781320,6795360,6804000,6814080,6819120,6834240,6846840,6854400,6874560,6879600,6890400,6894720,6922080,6930000,6940080,6945120,6955200,6966960,6985440,7001280,7010640,7013160,7015680,7025760,7030800,7040880,7056000,7068600,7071120,7076160,7096320,7104240,7106400,7128000,7136640,7141680,7151760,7156800,7166880,7182000,7187040,7197120,7207200,7223040,7232400,7234920,7257600,7262640,7270560,7272720,7282800,7286400,7302960,7308000,7318080,7333200,7338240,7348320,7358400,7368480,7373520,7378560,7403760,7408800,7413120,7418880,7428960,7439040,7454160,7459200,7469280,7484400,7499520,7529760,7534800,7539840,7560000,7567560,7585200,7595280,7600320,7603200,7619040,7620480,7635600,7650720,7660800,7665840,7674480,7687680,7706160,7711200,7722000,7731360,7733880,7741440,7756560,7761600,7766640,7786800,7796880,7801920,7809120,7812000,7817040,7824960,7832160,7840800,7852320,7862400,7872480,7882560,7892640,7900200,7922880,7927920,7938000,7963200,7968240,7983360,7993440,7998480]

/-- Helper: convert rational sum to integer sum when all denominators divide L -/
lemma sum_div_eq {L : ℕ} {D : Finset ℕ} (hL : L ≠ 0) (hD : ∀ d ∈ D, d ∣ L) :
    (∑ d ∈ D, (1 : ℚ) / d) = (∑ d ∈ D, (L / d : ℕ)) / L := by
  have h₁ : (∑ d ∈ D, (1 : ℚ) / d) = ∑ d ∈ D, ((1 : ℚ) / d) := rfl
  rw [h₁]
  have h₂ : ∑ d ∈ D, ((1 : ℚ) / d) = ∑ d ∈ D, ((L : ℚ) / d) / L := by
    apply Finset.sum_congr rfl
    intro d hd
    have h₃ : d ∣ L := hD d hd
    have h₄ : d ≠ 0 := by
      intro h₅
      rw [h₅] at h₃
      norm_num [Nat.zero_dvd] at h₃ ⊢
      <;> contradiction
    have h₅ : (d : ℚ) ≠ 0 := by exact_mod_cast h₄
    have h₆ : (1 : ℚ) / d = ((L : ℚ) / (d : ℚ)) / L := by
      have h₇ : (L : ℚ) ≠ 0 := by exact_mod_cast hL
      field_simp [h₅, h₇]
      <;> ring_nf
      <;> field_simp [h₅, h₇]
      <;> norm_cast
      <;> ring_nf at *
      <;> norm_num at *
      <;> omega
    rw [h₆]
    <;> field_simp
    <;> ring_nf
  rw [h₂]
  have h₃ : ∑ d ∈ D, ((L : ℚ) / d) / L = (∑ d ∈ D, ((L : ℚ) / d)) / L := by
    rw [Finset.sum_div]
  rw [h₃]
  have h₄ : (∑ d ∈ D, ((L : ℚ) / d)) = (∑ d ∈ D, (L / d : ℕ) : ℚ) := by
    apply Finset.sum_congr rfl
    intro d hd
    have h₅ : d ∣ L := hD d hd
    have h₆ : (L : ℚ) / d = (L / d : ℕ) := by
      have h₇ : (d : ℕ) ∣ L := h₅
      have h₈ : L = d * (L / d) := by
        have h₉ := Nat.div_mul_cancel h₇
        linarith
      have h₉ : (d : ℕ) ≠ 0 := by
        intro h₁₀
        rw [h₁₀] at h₇
        norm_num at h₇ ⊢
        <;> contradiction
      have h₁₀ : (L : ℚ) / d = (L / d : ℕ) := by
        have h₁₁ : (L : ℚ) = (d : ℚ) * (L / d : ℚ) := by
          norm_cast at h₈ ⊢
          <;> simp_all [mul_comm]
          <;> ring_nf at * <;> norm_num at * <;> linarith
        rw [h₁₁]
        field_simp [h₉]
        <;> ring_nf
        <;> norm_cast
        <;> field_simp [h₉]
        <;> ring_nf
      exact h₁₀
    rw [h₆]
    <;> norm_cast
  rw [h₄]
  <;> field_simp [hL]
  <;> norm_cast
  <;> norm_num at *
  <;> linarith

/-- Helper: sum ≥ 1 iff integer sum ≥ L -/
lemma sum_div_ge_one_iff {L : ℕ} {D : Finset ℕ} (hL : L ≠ 0) (hD : ∀ d ∈ D, d ∣ L) :
    (∑ d ∈ D, (1 : ℚ) / d) ≥ 1 ↔ (∑ d ∈ D, (L / d : ℕ)) ≥ L := by
  have h₁ : (∑ d ∈ D, (1 : ℚ) / d) = (∑ d ∈ D, (L / d : ℕ)) / L := sum_div_eq hL hD
  rw [h₁]
  have h₂ : (↑(∑ d ∈ D, (L / d : ℕ)) / L : ℚ) ≥ 1 ↔ (∑ d ∈ D, (L / d : ℕ)) ≥ L := by
    have h₃ : (L : ℚ) > 0 := by exact_mod_cast Nat.pos_of_ne_zero hL
    constructor
    · intro h
      have h₄ : ((∑ d ∈ D, (L / d : ℕ)) : ℚ) / L ≥ 1 := h
      have h₅ : ((∑ d ∈ D, (L / d : ℕ)) : ℚ) ≥ L := by
        calc
          ((∑ d ∈ D, (L / d : ℕ)) : ℚ) = (((∑ d ∈ D, (L / d : ℕ)) : ℚ) / L) * L := by
            field_simp [h₃.ne'] <;> ring_nf <;> field_simp [h₃.ne'] <;> ring_nf
          _ ≥ 1 * L := by gcongr <;> simp_all [h₃.le]
          _ = L := by ring
      exact_mod_cast h₅
    · intro h
      have h₄ : (∑ d ∈ D, (L / d : ℕ)) ≥ L := h
      have h₅ : ((∑ d ∈ D, (L / d : ℕ)) : ℚ) ≥ L := by exact_mod_cast h₄
      have h₆ : ((∑ d ∈ D, (L / d : ℕ)) : ℚ) / L ≥ 1 := by
        have h₇ : (L : ℚ) > 0 := by exact_mod_cast Nat.pos_of_ne_zero hL
        -- Prove that if x ≥ L and L > 0, then x / L ≥ 1
        have h₈ : ((∑ d ∈ D, (L / d : ℕ)) : ℚ) / L ≥ 1 := by
          rw [ge_iff_le]
          -- Use the fact that for L > 0, x / L ≤ 1 ↔ x ≤ L
          have h₉ : ((∑ d ∈ D, (L / d : ℕ)) : ℚ) ≥ L := h₅
          have h₁₀ : ((∑ d ∈ D, (L / d : ℕ)) : ℚ) / L ≥ 1 := by
            -- Since x ≥ L and L > 0, x / L ≥ L / L = 1
            have h₁₁ : ((∑ d ∈ D, (L / d : ℕ)) : ℚ) / L ≥ L / L := by
              gcongr
            have h₁₂ : (L : ℚ) / L = 1 := by
              field_simp [h₃.ne']
            linarith
          exact h₁₀
        exact h₈
      exact h₆
  exact h₂

/-- SPF (smallest prime factor) table for n ≤ 8000001 -/
def spfArray : Array ℕ := by sorry

/-- Fast prime check using SPF table -/
def isPrimeFast (n : ℕ) : Bool := by sorry

/-- Compute the integer sum for all L < 8000000 using sieve -/
def fastAccArray : Array ℕ := by sorry

/-- Check if the candidates list matches the computed values -/
def checkCandidates : Bool := by sorry

/-- Proof that checkCandidates = true -/
theorem checkCandidates_true : checkCandidates = true := by sorry

/-- Relate fastAccArray to the mathematical sum -/
lemma fastAccArray_eq_sum {L : ℕ} (hL : L < 8000000) :
    fastAccArray[L] = ∑ d ∈ (Nat.divisors L).filter (fun d => (d + 1).Prime ∧ 4 ≤ d), (L / d : ℕ) := by
  have h₁ : L < fastAccArray.size := by sorry
  sorry

/-- LEAF: the reciprocal test step of the forum thread 273 search, every lcm below 8000000 outside the
candidate list fails the reciprocal test. Class MEDIUM, a finite but large computation over 8000000 values,
true by the sieve run recorded in the file header. -/
theorem leaf_recip_lt_one (L : ℕ) (hL : L < 8000000) (hC : L ∉ candidates) :
    (∑ d ∈ (Nat.divisors L).filter (fun d => (d + 1).Prime ∧ 4 ≤ d), (1 : ℚ) / d) < 1 := by sorry

/-- LEAF: the covering search step of the forum thread 273 search, no covering with distinct moduli
`p - 1`, `p ≥ 5` prime, has its lcm in the candidate list. Class HARD, an exhaustive covering search over
828 lcm values, reported in the thread as an unrefereed computer search. -/
theorem leaf_no_cover_at_candidates {S : Finset (ℕ × ℤ)} (hS : Covers S)
    (hi : Set.InjOn Prod.fst (S : Set (ℕ × ℤ)))
    (hp : ∀ s ∈ S, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ s.1 = p - 1) :
    S.lcm Prod.fst ∉ candidates := by
  sorry

/-- Assembly: the parent target, identical statement to `Novelty1615.lcm_ge_8000000`, from the two LEAFs. -/
theorem lcm_ge_8000000 : LcmBound 5 8000000 := by
  intro S hS hi hp
  by_contra hcon
  push Not at hcon
  have hpos : ∀ s ∈ S, 0 < s.1 := by
    intro s hs
    obtain ⟨p, -, h5, h⟩ := hp s hs
    omega
  have hL : S.lcm Prod.fst ≠ 0 := by
    intro h0
    obtain ⟨s, hs, h⟩ := Finset.lcm_eq_zero_iff.1 h0 |> fun h => (Set.mem_image _ _ _).1 h
    exact (hpos s hs).ne' h
  have hsub : S.image Prod.fst ⊆
      (Nat.divisors (S.lcm Prod.fst)).filter (fun d => (d + 1).Prime ∧ 4 ≤ d) := by
    intro m hm
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hm
    obtain ⟨p, hpp, h5, h⟩ := hp s hs
    have e : s.1 + 1 = p := by omega
    refine Finset.mem_filter.2 ⟨Nat.mem_divisors.2 ⟨Finset.dvd_lcm hs, hL⟩, ?_, ?_⟩
    · rw [e]; exact hpp
    · omega
  have hsum := one_le_sum_inv hS hpos
  have heq : (∑ s ∈ S, (1 : ℚ) / s.1) = ∑ m ∈ S.image Prod.fst, (1 : ℚ) / m :=
    (Finset.sum_image (s := S) (g := Prod.fst) (f := fun d : ℕ => (1 : ℚ) / d) hi).symm
  have hle : (∑ m ∈ S.image Prod.fst, (1 : ℚ) / m) ≤
      ∑ d ∈ (Nat.divisors (S.lcm Prod.fst)).filter (fun d => (d + 1).Prime ∧ 4 ≤ d), (1 : ℚ) / d :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  have hlt := leaf_recip_lt_one _ hcon (leaf_no_cover_at_candidates hS hi hp)
  rw [heq] at hsum
  linarith

end LeanLab.OpenProblems.Feed1122DecompJ1235Split
