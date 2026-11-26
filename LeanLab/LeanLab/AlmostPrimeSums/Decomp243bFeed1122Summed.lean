import LeanLab.AlmostPrimeSums.Base243
import LeanLab.AlmostPrimeSums.Lower243
import LeanLab.AlmostPrimeSums.S146PiBounds

/-!
AI wrote this Lean code, burst S82 burst-20261122 feed1122. Binary Goldbach is open.
Split of `Decomp243b.summed_sieve_application` into leaves following
BJS https://arxiv.org/abs/2207.09452 pp. 52 to 54 equations 164 to 172.
For each middle prime `q` the sieve set is `A_q = {N - p : q ∣ N - p}`, of mass
`π(N)/(q - 1)` with density `g(d) = 1/φ(d)`, sifted to level `D/q`.
The parent is proved here from the leaves as `summed_sieve_application_of_leaves`,
over the definitions of `Base243` and `Decomp243a`, so `Decomp243b` can import this file.
-/

namespace LeanLab.AlmostPrimeSums.Decomp243bFeed1122Summed

open Finset Real Filter Topology LeanLab.ChenExplicit
open LeanLab.AlmostPrimeSums.Decomp1527a LeanLab.AlmostPrimeSums.Decomp1527c
open LeanLab.AlmostPrimeSums.Decomp243a LeanLab.AlmostPrimeSums.Decomp243b

noncomputable section

/-- The sifting primorial `P(z) = ∏_{2 < p < N^{1/8}, p ∤ N} p`, the product of the primes
indexing `sieveProduct N (1/8)`. BJS p. 37 equation 109 and p. 38 equation 119. -/
def summedPrimorial (N : ℕ) : ℕ :=
  ∏ p ∈ (range N).filter (fun p : ℕ => p.Prime ∧ 2 < p ∧
    (p : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 8) ∧ ¬ p ∣ N), p

/-- The summed remainder `Σ_q Σ_{d ∣ P(z), d < D/q} |#A_{qd} - π(N)/φ(qd)|` over the
primes `q` of `qSet`, with `D = sieveLevel N B`. BJS p. 3 equations 3 and 10,
specialised on p. 53 equations 168 to 171. -/
def summedRemainder (N : ℕ) (B : ℝ) : ℝ :=
  ∑ q ∈ qSet N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3)),
    ∑ d ∈ (summedPrimorial N).divisors.filter
        (fun d : ℕ => (d : ℝ) < sieveLevel N B / q),
      |(#((range N).filter (fun p => p.Prime ∧ ¬ p ∣ N ∧ q * d ∣ N - p)) : ℝ)
        - (Nat.primeCounting N : ℝ) / ((q * d).totient : ℝ)|

/-- LEAF: BJS pp. 52 to 53 equations 164 to 170, the upper linear sieve applied to each
`A_q` at `z = N^{1/8}`, level `D/q`, mass `π(N)/(q - 1)`, summed over `q`, with the sum
of `F(s_q)/(q - 1)` extended from `q ∤ N` to all middle primes, and a varying relative
error `O((log N)^{-1/3})`. Iwaniec 1980 Rosser sieve, or Halberstam and Richert
Theorem 8.4 with an improved error; Theorem 11.1 alone has the weaker error
`(log log D)^{3/4} (log D)^{-1/4}`. Class HARD. -/
theorem leaf_summed_linear_sieve_upper (B : ℝ) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, Even N → N₀ ≤ N →
      (sumSAq N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3)) : ℝ)
        ≤ (Nat.primeCounting N : ℝ) * sieveProduct N ((1 : ℝ) / 8) * primeCoefficient N B
          + C * ((Nat.primeCounting N : ℝ) * sieveProduct N ((1 : ℝ) / 8)) /
              log N ^ ((1 : ℝ) / 3)
          + summedRemainder N B := by
  sorry

/-- LEAF: BJS p. 53 equation 171, the bilinear remainder bound from Bombieri
Vinogradov: for some level exponent `B`, the summed remainder is at most
`C N / (log N)^3`. Moduli `qd < D` are squarefree; each is counted at most
`ω(qd)` times, absorbed by taking `A = 4` in `LevelBV`. Class HARD. -/
theorem leaf_summed_remainder_BV (h : LevelBV) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      summedRemainder N B ≤ C * N / log N ^ 3 := by
  obtain ⟨B0, C0, hBV⟩ := h 3 (by norm_num)
  refine ⟨max B0 4, |C0| + 2, by positivity, by positivity, 3, fun N hN => ?_⟩
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hL1 : 1 ≤ log (N : ℝ) := by
    rw [← log_exp 1]
    exact log_le_log (exp_pos 1) (by have := exp_one_lt_d9; linarith)
  set L := log (N : ℝ) with hL
  have hLpos : 0 < L := by linarith
  set B := max B0 4 with hBdef
  let a : ℕ → ℕ := fun q => if Nat.Coprime N q then N else 1
  have ha : ∀ q, Nat.Coprime (a q) q := by
    intro q; simp only [a]; split_ifs with hq
    · exact hq
    · exact Nat.coprime_one_left q
  have hBV' := hBV N (by omega) (fun _ => N) a (fun _ => le_rfl) ha
  have h3 : L ^ (3 : ℝ) = L ^ 3 := by exact_mod_cast Real.rpow_natCast L 3
  rw [h3] at hBV'
  have hcop : Nat.Coprime (summedPrimorial N) N := by
    unfold summedPrimorial
    apply Nat.Coprime.prod_left
    intro p hp
    have hp' := (mem_filter.mp hp).2
    exact (Nat.Prime.coprime_iff_not_dvd hp'.1).mpr hp'.2.2.2
  set z : ℝ := (N : ℝ) ^ ((1 : ℝ) / 8) with hz
  have hsmall : ∀ p : ℕ, p.Prime → p ∣ summedPrimorial N → (p : ℝ) < z := by
    intro p hp hpd
    unfold summedPrimorial at hpd
    obtain ⟨r, hr, hpr⟩ := (Nat.Prime.prime hp).dvd_finset_prod_iff _ |>.mp hpd
    have hr' := (mem_filter.mp hr).2
    have : p = r := (Nat.prime_dvd_prime_iff_eq hp hr'.1).mp hpr
    subst this; exact hr'.2.2.1
  set T := (qSet N z ((N : ℝ) ^ ((1 : ℝ) / 3))).sigma (fun q => (summedPrimorial N).divisors.filter
      (fun d : ℕ => (d : ℝ) < sieveLevel N B / q)) with hT
  set S := T.image (fun x => x.1 * x.2) with hS
  have hrw : summedRemainder N B = ∑ m ∈ S,
      |(#((range N).filter (fun p => p.Prime ∧ ¬ p ∣ N ∧ m ∣ N - p)) : ℝ)
        - (Nat.primeCounting N : ℝ) / (m.totient : ℝ)| := by
    unfold summedRemainder
    rw [Finset.sum_sigma', hS, Finset.sum_image]
    intro x hx y hy hxy
    have hx' := mem_sigma.mp hx
    have hy' := mem_sigma.mp hy
    have hq1 := (mem_filter.mp hx'.1).2
    have hq2 := (mem_filter.mp hy'.1).2
    have hd2 := Nat.dvd_of_mem_divisors (mem_filter.mp hy'.2).1
    have hxy' : x.1 * x.2 = y.1 * y.2 := hxy
    have hdv : x.1 ∣ y.1 * y.2 := hxy' ▸ dvd_mul_right _ _
    have h1 : x.1 = y.1 := by
      rcases (Nat.Prime.dvd_mul hq1.1).mp hdv with h | h
      · exact (Nat.prime_dvd_prime_iff_eq hq1.1 hq2.1).mp h
      · exfalso
        have := hsmall _ hq1.1 (h.trans hd2)
        linarith [hq1.2.1]
    have h2 : x.2 = y.2 := by
      rw [h1] at hxy'
      exact Nat.eq_of_mul_eq_mul_left hq2.1.pos hxy'
    exact Sigma.ext h1 (heq_of_eq h2)
  have hmem : ∀ m ∈ S, 0 < m ∧ (m : ℝ) < sieveLevel N B ∧ Nat.Coprime N m := by
    intro m hm
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hm
    have hx' := mem_sigma.mp hx
    have hq1 := (mem_filter.mp hx'.1).2
    obtain ⟨hd1, hd2⟩ := mem_filter.mp hx'.2
    have hdpos : 0 < x.2 := Nat.pos_of_mem_divisors hd1
    have hqpos : (0 : ℝ) < x.1 := by exact_mod_cast hq1.1.pos
    refine ⟨Nat.mul_pos hq1.1.pos hdpos, ?_, ?_⟩
    · push_cast
      have := (lt_div_iff₀ hqpos).mp hd2
      linarith
    · apply Nat.Coprime.mul_right
      · exact Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hq1.1).mpr hq1.2.2)
      · exact Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_divisors hd1) hcop
          |> Nat.coprime_comm.mp
  have hLB : L ^ B0 ≤ L ^ B := rpow_le_rpow_of_exponent_le hL1 (le_max_left _ _)
  have hsqrt : 0 ≤ √(N : ℝ) := Real.sqrt_nonneg _
  have hDle : sieveLevel N B ≤ √(N : ℝ) / L ^ B0 :=
    div_le_div_of_nonneg_left hsqrt (rpow_pos_of_pos hLpos _) hLB
  have hSsub : S ⊆ Icc 1 ⌊√(N : ℝ) / L ^ B0⌋₊ := by
    intro d hd
    obtain ⟨hdpos, hd2, -⟩ := hmem d hd
    refine mem_Icc.mpr ⟨hdpos, Nat.le_floor ?_⟩
    linarith
  have hScard : (#S : ℝ) ≤ sieveLevel N B := by
    have h1 : #S ≤ ⌊sieveLevel N B⌋₊ := by
      have : S ⊆ Icc 1 ⌊sieveLevel N B⌋₊ := by
        intro d hd
        obtain ⟨hdpos, hd2, -⟩ := hmem d hd
        exact mem_Icc.mpr ⟨hdpos, Nat.le_floor hd2.le⟩
      simpa using card_le_card this
    have hD0 : 0 ≤ sieveLevel N B := by unfold sieveLevel; positivity
    calc (#S : ℝ) ≤ (⌊sieveLevel N B⌋₊ : ℝ) := by exact_mod_cast h1
      _ ≤ _ := Nat.floor_le hD0
  have hLB4 : L ^ (4 : ℕ) ≤ L ^ B := by
    rw [← Real.rpow_natCast]; exact rpow_le_rpow_of_exponent_le hL1 (by simp [hBdef])
  -- prime divisors of N
  set E := (range (N + 1)).filter (fun p => p.Prime ∧ p ∣ N) with hE
  have hEsub : E ⊆ N.primeFactors := by
    intro p hp
    obtain ⟨-, hp1, hp2⟩ := mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨hp1, hp2, by omega⟩
  have hEcard : (#E : ℝ) ≤ 2 * L := by
    have h2 : 2 ^ #N.primeFactors ≤ N := by
      calc 2 ^ #N.primeFactors = ∏ _p ∈ N.primeFactors, 2 := by simp
        _ ≤ ∏ p ∈ N.primeFactors, p :=
            Finset.prod_le_prod (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
        _ ≤ N := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd N)
    have h2r : (2 : ℝ) ^ #N.primeFactors ≤ N := by exact_mod_cast h2
    have hlog : (#N.primeFactors : ℝ) * log 2 ≤ L := by
      rw [← Real.log_pow]; exact log_le_log (by positivity) h2r
    have hl2 : (1 : ℝ) / 2 < log 2 := by have := Real.log_two_gt_d9; linarith
    have hc : (#E : ℝ) ≤ #N.primeFactors := by exact_mod_cast card_le_card hEsub
    nlinarith
  -- termwise bound
  have hterm : ∀ d ∈ S,
      |(#((range N).filter (fun p => p.Prime ∧ ¬ p ∣ N ∧ d ∣ N - p)) : ℝ)
        - (Nat.primeCounting N : ℝ) / (d.totient : ℝ)| ≤
      |(primesAP N d (a d) : ℝ) - (Nat.primeCounting N : ℝ) / (d.totient : ℝ)| + 2 * L := by
    intro d hd
    have hdcop : Nat.Coprime N d := (hmem d hd).2.2
    have had : a d = N := by
      show (if N.Coprime d then N else 1) = N
      exact if_pos hdcop
    rw [had]
    set Ad := (range N).filter (fun p => p.Prime ∧ ¬ p ∣ N ∧ d ∣ N - p)
    set AP := (range (N + 1)).filter (fun p => p.Prime ∧ p % d = N % d)
    have hAP : primesAP N d N = #AP := rfl
    have hsub1 : Ad ⊆ AP := by
      intro p hp
      obtain ⟨hp0, hp1, -, hp3⟩ := mem_filter.mp hp
      have hpN : p < N := mem_range.mp hp0
      refine mem_filter.mpr ⟨mem_range.mpr (by omega), hp1, ?_⟩
      exact ((Nat.modEq_iff_dvd' hpN.le).mpr hp3)
    have hsub2 : AP ⊆ Ad ∪ E := by
      intro p hp
      obtain ⟨hp0, hp1, hp3⟩ := mem_filter.mp hp
      have hpN : p ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hp0)
      by_cases hpd : p ∣ N
      · exact mem_union_right _ (mem_filter.mpr ⟨hp0, hp1, hpd⟩)
      · have hpN' : p < N := lt_of_le_of_ne hpN (fun h => hpd (h ▸ dvd_rfl))
        exact mem_union_left _ (mem_filter.mpr ⟨mem_range.mpr hpN', hp1, hpd,
          (Nat.modEq_iff_dvd' hpN).mp hp3⟩)
    have c1 : (#Ad : ℝ) ≤ #AP := by exact_mod_cast card_le_card hsub1
    have c2 : (#AP : ℝ) ≤ #Ad + #E := by
      exact_mod_cast (card_le_card hsub2).trans (card_union_le _ _)
    rw [hAP]
    have := abs_sub_le (#Ad : ℝ) (#AP) ((Nat.primeCounting N : ℝ) / (d.totient : ℝ))
    have h4 : |(#Ad : ℝ) - #AP| ≤ #E := by
      rw [abs_sub_le_iff]; constructor <;> linarith [(Nat.cast_nonneg (#E) : (0:ℝ) ≤ #E)]
    linarith
  -- assemble
  have hsum1 : summedRemainder N B ≤
      ∑ d ∈ S, (|(primesAP N d (a d) : ℝ) - (Nat.primeCounting N : ℝ) / (d.totient : ℝ)|
        + 2 * L) := by rw [hrw]; exact sum_le_sum hterm
  rw [sum_add_distrib, sum_const, nsmul_eq_mul] at hsum1
  have hsum2 : ∑ d ∈ S, |(primesAP N d (a d) : ℝ) - (Nat.primeCounting N : ℝ) / (d.totient : ℝ)|
      ≤ C0 * N / L ^ 3 :=
    (sum_le_sum_of_subset_of_nonneg hSsub (fun _ _ _ => abs_nonneg _)).trans hBV'
  have hL3 : 0 < L ^ 3 := by positivity
  have hC0 : C0 * N / L ^ 3 ≤ |C0| * N / L ^ 3 := by
    gcongr; exact le_abs_self C0
  have hD2 : sieveLevel N B * (2 * L) ≤ 2 * N / L ^ 3 := by
    have hLBpos : 0 < L ^ B := rpow_pos_of_pos hLpos _
    have hsq : √(N : ℝ) ≤ N := by
      exact Real.sqrt_le_iff.mpr ⟨hNpos.le, by nlinarith⟩
    unfold sieveLevel
    rw [← hL]
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hLBpos hL3]
    have : L ^ 4 = L * L ^ 3 := by ring
    calc √(N : ℝ) * (2 * L) * L ^ 3 = 2 * √(N : ℝ) * L ^ 4 := by ring
      _ ≤ 2 * N * L ^ B := by gcongr
  have hSL : (#S : ℝ) * (2 * L) ≤ sieveLevel N B * (2 * L) :=
    mul_le_mul_of_nonneg_right hScard (by linarith)
  calc summedRemainder N B ≤ C0 * N / L ^ 3 + 2 * N / L ^ 3 := by linarith
    _ ≤ |C0| * N / L ^ 3 + 2 * N / L ^ 3 := by linarith
    _ = (|C0| + 2) * N / L ^ 3 := by ring

/-- LEAF: Rosser and Schoenfeld 1962 Theorem 1 equation 3.2,
`π(x) < x/log x · (1 + 3/(2 log x))` for `x > 1`, in the weaker eventual form
`π(N) ≤ N/log N + 2N/(log N)^2`; passes from `X = π(N)` to the ideal mass of
BJS p. 52 equation 164. Class MEDIUM. -/
theorem leaf_pi_upper_sharp : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    (Nat.primeCounting N : ℝ) ≤ N / log N + 2 * N / log N ^ 2 :=
  LeanLab.AlmostPrimeSums.S146PiBounds.pi_upper_nat

/-- A uniform positive lower bound for `U_N`. -/
theorem U_ge' (N : ℕ) : 2 * exp (-eulerMascheroniConstant) * twinC ≤ U N := by
  unfold U
  have h1 := one_le_oddFactor N
  have h2 : 0 ≤ 2 * exp (-eulerMascheroniConstant) * twinC := by
    have := twinC_pos; positivity
  calc 2 * exp (-eulerMascheroniConstant) * twinC
      = 2 * exp (-eulerMascheroniConstant) * twinC * 1 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 h2

/-- The parent `summed_sieve_application`, assembled from the three leaves and the
proved prime coefficient limit. CONDITIONAL ON LevelBV and the open leaves above. -/
theorem summed_sieve_application_of_leaves (h : LevelBV) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ,
      Even N → N₀ ≤ N →
      (sumSAq N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3)) : ℝ) / 2
        ≤ summedMain N B + C * sieveError N := by
  obtain ⟨B, C2, hB, hC2, N2, h2⟩ := leaf_summed_remainder_BV h
  obtain ⟨C1, hC1, N1, h1⟩ := leaf_summed_linear_sieve_upper B hB
  obtain ⟨N4, h4⟩ := leaf_pi_upper_sharp
  set K : ℝ := 1 / (2 * exp eulerMascheroniConstant * (1 / 8)) + 1 with hK
  have hKpos : 0 < K := by rw [hK]; positivity
  have hratio := (idealMass_ratio (1 / 8) (by norm_num) (by norm_num)).eventually
    (gt_mem_nhds (show 1 / (2 * exp eulerMascheroniConstant * (1 / 8)) < K by rw [hK]; linarith))
  obtain ⟨N5, h5⟩ := eventually_atTop.mp hratio
  set K2 : ℝ := exp eulerMascheroniConstant * log 6 / 2 + 1 with hK2
  have hlog6 : 0 < log (6 : ℝ) := log_pos (by norm_num)
  have hK2pos : 0 < K2 := by rw [hK2]; positivity
  have hpc := LeanLab.AlmostPrimeSums.Lower243.primeCoefficient_limit B hB
  have hpc1 := hpc.eventually (gt_mem_nhds (show exp eulerMascheroniConstant * log 6 / 2 < K2 by
    rw [hK2]; linarith))
  have hpc0 := hpc.eventually (lt_mem_nhds (show (0 : ℝ) < exp eulerMascheroniConstant * log 6 / 2
    by positivity))
  obtain ⟨N6, h6⟩ := eventually_atTop.mp (hpc1.and hpc0)
  set c0 : ℝ := 2 * exp eulerMascheroniConstant * (2 * exp (-eulerMascheroniConstant) * twinC)
    with hc0
  have hc0pos : 0 < c0 := by have := twinC_pos; rw [hc0]; positivity
  refine ⟨B, K * K2 + 3 * C1 * K + C2 / c0, hB, by positivity,
    max (max (max N1 N2) (max N4 N5)) (max N6 3), fun N hEven hN => ?_⟩
  simp only [max_le_iff] at hN
  obtain ⟨⟨⟨hN1, hN2⟩, hN4, hN5⟩, hN6, hN7⟩ := hN
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN7
  have hNpos : (0 : ℝ) < N := by linarith
  have hL1 : 1 ≤ log (N : ℝ) := by
    rw [← log_exp 1]
    exact log_le_log (exp_pos 1) (by have := exp_one_lt_d9; linarith)
  have hLpos : 0 < log (N : ℝ) := by linarith
  set L := log (N : ℝ) with hL
  set P := sieveProduct N ((1 : ℝ) / 8)
  set pc := primeCoefficient N B
  set pi : ℝ := (Nat.primeCounting N : ℝ)
  have hP : 0 < P := sieveProduct_pos _ _
  have hM : 0 < Mchen N := Mchen_pos N (by omega)
  have hA := h1 N hEven hN1
  have hR := h2 N hN2
  have hpu := h4 N hN4
  have hI := h5 N hN5
  obtain ⟨hpcK, hpc0'⟩ := h6 N hN6
  have hI' : idealMass N (1 / 8) ≤ K * Mchen N := by
    have := (div_lt_iff₀ hM).mp hI; linarith
  have hidl : idealMass N (1 / 8) = N / L * P := rfl
  have hidpos : 0 ≤ idealMass N (1 / 8) := by rw [hidl]; positivity
  have hL14 : 0 < L ^ ((1 : ℝ) / 4) := rpow_pos_of_pos hLpos _
  have hL13 : 0 < L ^ ((1 : ℝ) / 3) := rpow_pos_of_pos hLpos _
  have h1413 : L ^ ((1 : ℝ) / 4) ≤ L ^ ((1 : ℝ) / 3) :=
    rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have h14L : L ^ ((1 : ℝ) / 4) ≤ L := by
    calc L ^ ((1 : ℝ) / 4) ≤ L ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      _ = L := rpow_one L
  have hSE : sieveError N = Mchen N / L ^ ((1 : ℝ) / 4) := rfl
  have hSEpos : 0 ≤ sieveError N := by rw [hSE]; positivity
  -- π(N) ≤ 3 N / log N
  have hpi3 : pi * P ≤ 3 * idealMass N (1 / 8) := by
    have : 2 * N / L ^ 2 ≤ 2 * N / L := by
      apply div_le_div_of_nonneg_left (by positivity) hLpos
      nlinarith
    calc pi * P ≤ (N / L + 2 * N / L) * P := mul_le_mul_of_nonneg_right (by linarith) hP.le
      _ = 3 * idealMass N (1 / 8) := by rw [hidl]; ring
  -- main term
  have hmain : pi * P * pc ≤ 2 * summedMain N B + 2 * K * K2 * sieveError N := by
    have hstep : pi * P * pc ≤ (N / L + 2 * N / L ^ 2) * P * pc :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpu hP.le) hpc0'.le
    have hsplit : (N / L + 2 * N / L ^ 2) * P * pc =
        2 * summedMain N B + 2 * (idealMass N (1 / 8) * pc) / L := by
      simp only [summedMain, hidl]; field_simp; ring
    have hx : idealMass N (1 / 8) * pc ≤ K * Mchen N * K2 :=
      mul_le_mul hI' hpcK.le hpc0'.le (by positivity)
    have hy : 2 * (idealMass N (1 / 8) * pc) / L ≤ 2 * (K * Mchen N * K2) / L ^ ((1 : ℝ) / 4) :=
      div_le_div₀ (by positivity) (by linarith) hL14 h14L
    have hz : 2 * (K * Mchen N * K2) / L ^ ((1 : ℝ) / 4) = 2 * K * K2 * sieveError N := by
      rw [hSE]; ring
    linarith
  -- relative sieve error
  have hE1 : C1 * (pi * P) / L ^ ((1 : ℝ) / 3) ≤ 2 * (3 * C1 * K) * sieveError N := by
    have hpiP : pi * P ≤ 3 * K * Mchen N := by linarith
    calc C1 * (pi * P) / L ^ ((1 : ℝ) / 3) ≤ C1 * (3 * K * Mchen N) / L ^ ((1 : ℝ) / 4) := by
          apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hpiP hC1.le) hL14 h1413
      _ ≤ 2 * (3 * C1 * K) * sieveError N := by
          rw [hSE]
          have : 0 ≤ C1 * (3 * K * Mchen N) / L ^ ((1 : ℝ) / 4) := by positivity
          have he : 2 * (3 * C1 * K) * (Mchen N / L ^ ((1 : ℝ) / 4)) =
            2 * (C1 * (3 * K * Mchen N) / L ^ ((1 : ℝ) / 4)) := by ring
          rw [he]; linarith
  -- remainder
  have hE2 : summedRemainder N B ≤ 2 * (C2 / c0) * sieveError N := by
    have hU := U_ge' N
    have hMc : c0 * N / L ^ 2 ≤ Mchen N := by
      simp only [Mchen, hc0]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have : 0 ≤ (N : ℝ) := hNpos.le
      calc 2 * exp eulerMascheroniConstant * (2 * exp (-eulerMascheroniConstant) * twinC) * N
          = 2 * exp eulerMascheroniConstant * ((2 * exp (-eulerMascheroniConstant) * twinC) * N)
            := by ring
        _ ≤ 2 * exp eulerMascheroniConstant * (U N * N) := by gcongr
        _ = _ := by ring
    have hb : summedRemainder N B ≤ C2 / c0 * sieveError N := by
      calc summedRemainder N B ≤ C2 * N / L ^ 3 := hR
        _ ≤ C2 * N / (L ^ 2 * L ^ ((1 : ℝ) / 4)) := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            rw [pow_succ]; exact mul_le_mul_of_nonneg_left h14L (by positivity)
        _ = C2 / c0 * ((c0 * N / L ^ 2) / L ^ ((1 : ℝ) / 4)) := by
            field_simp
        _ ≤ C2 / c0 * (Mchen N / L ^ ((1 : ℝ) / 4)) := by
            gcongr
        _ = C2 / c0 * sieveError N := by rw [hSE]
    have : 0 ≤ C2 / c0 * sieveError N := by positivity
    linarith
  have hfin : (sumSAq N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3)) : ℝ)
      ≤ 2 * (summedMain N B + (K * K2 + 3 * C1 * K + C2 / c0) * sieveError N) := by
    have := hA
    nlinarith only [this, hmain, hE1, hE2]
  linarith

end

#print axioms summed_sieve_application_of_leaves
#print axioms U_ge'

end LeanLab.AlmostPrimeSums.Decomp243bFeed1122Summed
