import LeanLab.ChenDoubleSieve.Decomp363c
import LeanLab.PNTPort.BVMax.PrimesUncond

/-!
The two analytic inputs in the written proof of Wu 2004 equation 10.2.
The linear sieve retains the arithmetic progression discrepancy.
The mean value input contains neither a sifted count nor the lower function.
Source: https://arxiv.org/pdf/0705.1652, page 6 and page 38.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task363
open Task275 Task348
open Wu04Functional (IsLinearSieve)

/-- The finite level Q used before equation 10.2. -/
def sieveLevel (B : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B

/-- Squarefree moduli up to Q that are coprime to N.
One is present when Q is at least one. The moduli need not have all prime
factors below the sifting level. -/
def remainderModuli (B : ℝ) (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 ⌊sieveLevel B N⌋₊).filter (fun q => Squarefree q ∧ q.Coprime N)

/-- The absolute discrepancy sum dominated by Lemma 2.3 on page 38.
Only the fixed endpoint N and residue N are needed here. -/
def rawRemainder (B : ℝ) (N : ℕ) : ℝ :=
  ∑ q ∈ remainderModuli B N,
    |(#((primeSequence N).filter (fun a => q ∣ a)) : ℝ) -
      Wu04.li N / (q.totient : ℝ)|

/-- The discrepancy is nonnegative for every finite parameter choice. -/
theorem rawRemainder_nonneg (B : ℝ) (N : ℕ) : 0 ≤ rawRemainder B N := by
  exact Finset.sum_nonneg (fun q _ => abs_nonneg _)

/-- LEAF. Wu 2004 page 6 Lemma 2.2 equation 2.5, specialized on page 38.
Retain the li main term, the relative sieve error and the discrepancy sum
with its fixed sieve constant.
This estimate has not used the mean value theorem of Lemma 2.3. -/
theorem linear_sieve_with_remainder (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ B : ℝ, 0 < B → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
        liMain0 f B N - δ * (Wu04.li N * lowerDensity N) -
          C * rawRemainder B N ≤ sieveTerms N 0 := by
  sorry

section Helpers363b

open LeanLab.PNTPort.BVMax

/-- The antitone integrand of the logarithmic integral on `[2, N]`. -/
private theorem antitone_invlog (N : ℕ) (hN : 2 ≤ N) :
    AntitoneOn (fun t : ℝ => (Real.log t)⁻¹) (Set.Icc (2:ℝ) N) := by
  intro x hx y hy hxy
  simp only
  apply inv_anti₀
  · exact Real.log_pos (by linarith [hx.1])
  · exact Real.log_le_log (by linarith [hx.1]) hxy

/-- `liD N` as a sum from two. -/
private theorem liD_eq (N : ℕ) (hN : 1 ≤ N) :
    liD (N : ℝ) = ∑ n ∈ Finset.Icc 2 N, (Real.log n)⁻¹ := by
  unfold liD liN
  rw [Nat.floor_natCast]
  have h : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [h, sum_insert (by simp)]
  simp [Real.log_one]

/-- The continuous logarithmic integral is below the discrete one. -/
private theorem li_le_liD (N : ℕ) (hN : 2 ≤ N) : Wu04.li N ≤ liD (N : ℝ) := by
  have hanti := antitone_invlog N hN
  have h1 : Wu04.li N ≤ ∑ x ∈ Finset.Ico 2 N, (Real.log x)⁻¹ := by
    simpa [Wu04.li] using
      AntitoneOn.integral_le_sum_Ico (f := fun t : ℝ => (Real.log t)⁻¹) hN hanti
  have h2 : ∑ x ∈ Finset.Ico 2 N, (Real.log x)⁻¹ ≤ ∑ x ∈ Finset.Icc 2 N, (Real.log x)⁻¹ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Ico_subset_Icc_self) (fun _ _ _ => by positivity)
  rw [liD_eq N (by omega)]
  linarith

/-- The discrete logarithmic integral exceeds the continuous one by at most `2 / log 2`. -/
private theorem liD_le_li (N : ℕ) (hN : 2 ≤ N) : liD (N : ℝ) ≤ Wu04.li N + 2 / Real.log 2 := by
  have hanti := antitone_invlog N hN
  have h1 : ∑ i ∈ Finset.Ico 2 N, (Real.log (i+1:ℕ))⁻¹ ≤ Wu04.li N := by
    simpa [Wu04.li] using
      AntitoneOn.sum_le_integral_Ico (f := fun t : ℝ => (Real.log t)⁻¹) hN hanti
  have hsplit : Finset.Icc 2 N = insert 2 (Finset.Icc 3 N) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have himg : Finset.Icc 3 N = (Finset.Ico 2 N).image (fun i => i + 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ico, Finset.mem_image]
    constructor
    · intro h; exact ⟨n - 1, by omega, by omega⟩
    · rintro ⟨i, h, rfl⟩; omega
  have hsum : ∑ n ∈ Finset.Icc 3 N, (Real.log n)⁻¹ =
      ∑ i ∈ Finset.Ico 2 N, (Real.log ((i+1 : ℕ) : ℝ))⁻¹ := by
    rw [himg, Finset.sum_image]
    intro i hi j hj hij
    simp only at hij
    omega
  rw [liD_eq N (by omega), hsplit, sum_insert (by simp), hsum]
  have h2 : (Real.log (2:ℕ))⁻¹ = (Real.log 2)⁻¹ := by norm_num
  have h3 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h4 : (0:ℝ) ≤ (Real.log 2)⁻¹ := by positivity
  rw [h2, div_eq_mul_inv]
  linarith

/-- The comparison of the discrete and continuous logarithmic integrals. -/
private theorem abs_liD_sub_li (N : ℕ) (hN : 2 ≤ N) :
    |liD (N : ℝ) - Wu04.li N| ≤ 2 / Real.log 2 := by
  have h1 := li_le_liD N hN
  have h2 := liD_le_li N hN
  rw [abs_le]
  constructor <;> linarith


/-- The sieve remainder of `primeSequence N` at modulus `d` is `π(N; d, N)`. -/
private theorem card_dvd_primeSequence (N d : ℕ) (hd : 1 ≤ d) :
    (((primeSequence N).filter (fun m => d ∣ m)).card : ℝ) = piN N d N := by
  unfold primeSequence piN
  rw [filter_image, card_image_of_injOn]
  · congr 2
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc, Function.comp]
    constructor
    · rintro ⟨⟨hp, hpr⟩, hdvd⟩
      exact ⟨⟨hpr.one_lt.le, by omega⟩, ((Nat.modEq_iff_dvd' (by omega)).mpr hdvd), hpr⟩
    · rintro ⟨⟨h1, h2⟩, hmod, hpr⟩
      exact ⟨⟨by omega, hpr⟩, (Nat.modEq_iff_dvd' (by omega)).mp hmod⟩
  · intro a ha b hb he
    simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_range, Set.mem_ofPred_eq] at ha hb
    simp only at he
    omega

/-- The Bombieri-Vinogradov mean value bound for the difference sequence
`{N - p : p ≤ N prime}`, unconditional through `bvPi`. -/
private theorem bvPrimeSequence (A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
      ∑ d ∈ (Finset.Icc 1 ⌊Real.sqrt N / Real.log N ^ B⌋₊).filter
          (fun d => Nat.Coprime N d),
        |((((primeSequence N).filter (fun m => d ∣ m)).card : ℕ) : ℝ) -
          liD (N : ℝ) / (d.totient : ℝ)| ≤ K * N / Real.log N ^ A := by
  obtain ⟨B, hB, K, hK⟩ := bvPi A hA
  refine ⟨B, hB, K, fun N hN => ?_⟩
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  set a : ℕ → ℕ := fun d => if Nat.Coprime N d then N else 1 with ha
  have hacop : ∀ d, Nat.Coprime (a d) d := by
    intro d; simp only [ha]; split_ifs with h
    · exact h
    · exact Nat.coprime_one_left d
  have hbv := hK N hN2 a hacop (fun _ => (N : ℝ)) (fun _ => ⟨by positivity, le_rfl⟩)
  refine le_trans ?_ hbv
  have hEq : ∀ d ∈ (Finset.Icc 1 ⌊Real.sqrt N / Real.log N ^ B⌋₊).filter
        (fun d => Nat.Coprime N d),
      |((((primeSequence N).filter (fun m => d ∣ m)).card : ℕ) : ℝ) -
          liD (N : ℝ) / (d.totient : ℝ)|
        = |piAP (N : ℝ) d (a d) - liD (N : ℝ) / (d.totient : ℝ)| := by
    intro d hd
    rw [mem_filter] at hd
    have had : a d = N := by simp only [ha]; rw [if_pos hd.2]
    rw [had, card_dvd_primeSequence N d (by rw [Finset.mem_Icc] at hd; omega)]
    simp only [piAP, Nat.floor_natCast]
  calc ∑ d ∈ (Finset.Icc 1 ⌊Real.sqrt N / Real.log N ^ B⌋₊).filter
          (fun d => Nat.Coprime N d),
        |((((primeSequence N).filter (fun m => d ∣ m)).card : ℕ) : ℝ) -
            liD (N : ℝ) / (d.totient : ℝ)|
      = ∑ d ∈ (Finset.Icc 1 ⌊Real.sqrt N / Real.log N ^ B⌋₊).filter
          (fun d => Nat.Coprime N d),
        |piAP (N : ℝ) d (a d) - liD (N : ℝ) / (d.totient : ℝ)| :=
        sum_congr rfl hEq
    _ ≤ ∑ d ∈ Finset.Icc 1 ⌊Real.sqrt N / Real.log N ^ B⌋₊,
        |piAP (N : ℝ) d (a d) - liD (N : ℝ) / (d.totient : ℝ)| :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => abs_nonneg _)


/-- `sieveLevel` is the classical level `√N / (log N)^B`. -/
private theorem sieveLevel_eq (B : ℝ) (N : ℕ) :
    sieveLevel B N = Real.sqrt N / Real.log N ^ B := by
  unfold sieveLevel
  rw [Real.sqrt_eq_rpow]

/-- `log 3 > 1`, in the form used below. -/
private theorem one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  have h := Real.log_three_near_10
  rw [abs_le] at h
  nlinarith [h.1]

end Helpers363b

/-- LEAF. Wu 2004 page 6 Lemma 2.3 and page 38 remainder display.
Specialize to the single multiplier one, the endpoint N and residue N.
The estimate has no linear sieve function and no sifted count. -/
theorem remainder_log_cubic : ∃ B : ℝ, 0 < B ∧ ∃ D : ℝ, 0 ≤ D ∧
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      rawRemainder B N ≤ D * (N : ℝ) / log N ^ 3 := by
  obtain ⟨B, hB, K, hbv⟩ := bvPrimeSequence 3 (by norm_num)
  obtain ⟨K2, hK2pos, hK2⟩ := LeanLab.PNTPort.BV.log_rpow_le_sqrt (3 : ℝ)
  refine ⟨B, hB, max 0 K + 4 * K2 / Real.log 2, by positivity, 4, ?_⟩
  intro N hEven hN
  have h3 : 3 ≤ N := by omega
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast (by omega : 2 ≤ N)
  have hNpos : (0 : ℝ) < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  have hlog3 : 0 < Real.log N ^ 3 := by positivity
  have hconv : Real.log (N : ℝ) ^ (3 : ℝ) = Real.log (N : ℝ) ^ 3 := Real.rpow_natCast _ _
  have hlog1 : 1 ≤ Real.log N :=
    (one_le_log_three.trans (Real.log_le_log (by norm_num) (by exact_mod_cast h3 : (3:ℝ) ≤ N)))
  have hlevN : ⌊sieveLevel B N⌋₊ = ⌊Real.sqrt N / Real.log N ^ B⌋₊ := by
    rw [sieveLevel_eq]
  set Q := ⌊Real.sqrt N / Real.log N ^ B⌋₊ with hQ
  have hC0 : (0 : ℝ) ≤ 2 / Real.log 2 := by
    have : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  -- (1) split the main term
  have stepA : rawRemainder B N ≤
      ∑ q ∈ remainderModuli B N,
        |((((primeSequence N).filter (fun m => q ∣ m)).card : ℕ) : ℝ) -
            LeanLab.PNTPort.BVMax.liD (N : ℝ) / (q.totient : ℝ)| + (#(remainderModuli B N) : ℝ) * (2 / Real.log 2) := by
    have hper : ∀ q ∈ remainderModuli B N,
        |((((primeSequence N).filter (fun m => q ∣ m)).card : ℕ) : ℝ) -
            Wu04.li N / (q.totient : ℝ)| ≤
          |((((primeSequence N).filter (fun m => q ∣ m)).card : ℕ) : ℝ) -
              LeanLab.PNTPort.BVMax.liD (N : ℝ) / (q.totient : ℝ)| + 2 / Real.log 2 := by
      intro q hq
      rw [remainderModuli, Finset.mem_filter, Finset.mem_Icc] at hq
      have hq1 : 1 ≤ q := hq.1.1
      have hφ : (1 : ℝ) ≤ (q.totient : ℝ) := by
        have := Nat.totient_pos.mpr (by omega : 0 < q)
        exact_mod_cast this
      have hφ0 : (0 : ℝ) < (q.totient : ℝ) := by linarith
      have hli := abs_liD_sub_li N (by omega)
      have hstep : |LeanLab.PNTPort.BVMax.liD (N : ℝ) / (q.totient : ℝ) - Wu04.li N / (q.totient : ℝ)| ≤
          2 / Real.log 2 := by
        have heq : LeanLab.PNTPort.BVMax.liD (N : ℝ) / (q.totient : ℝ) - Wu04.li N / (q.totient : ℝ) =
            (LeanLab.PNTPort.BVMax.liD (N : ℝ) - Wu04.li N) / (q.totient : ℝ) := by ring
        rw [heq, abs_div, abs_of_pos hφ0]
        calc |LeanLab.PNTPort.BVMax.liD (N : ℝ) - Wu04.li N| / (q.totient : ℝ) ≤
              (2 / Real.log 2) / (q.totient : ℝ) := by gcongr
          _ ≤ (2 / Real.log 2) / 1 := by
              exact div_le_div_of_nonneg_left hC0 (by norm_num) hφ
          _ = 2 / Real.log 2 := by norm_num
      calc |((((primeSequence N).filter (fun m => q ∣ m)).card : ℕ) : ℝ) -
              Wu04.li N / (q.totient : ℝ)|
          ≤ |((((primeSequence N).filter (fun m => q ∣ m)).card : ℕ) : ℝ) -
                LeanLab.PNTPort.BVMax.liD (N : ℝ) / (q.totient : ℝ)| +
              |LeanLab.PNTPort.BVMax.liD (N : ℝ) / (q.totient : ℝ) - Wu04.li N / (q.totient : ℝ)| := by
            simpa [Real.dist_eq] using dist_triangle
              ((((primeSequence N).filter (fun m => q ∣ m)).card : ℕ) : ℝ)
              (LeanLab.PNTPort.BVMax.liD (N : ℝ) / (q.totient : ℝ)) (Wu04.li N / (q.totient : ℝ))
        _ ≤ _ := by linarith
    calc rawRemainder B N
        = ∑ q ∈ remainderModuli B N,
            |((((primeSequence N).filter (fun m => q ∣ m)).card : ℕ) : ℝ) -
              Wu04.li N / (q.totient : ℝ)| := rfl
      _ ≤ ∑ q ∈ remainderModuli B N,
            (|((((primeSequence N).filter (fun m => q ∣ m)).card : ℕ) : ℝ) -
                LeanLab.PNTPort.BVMax.liD (N : ℝ) / (q.totient : ℝ)| + 2 / Real.log 2) :=
          Finset.sum_le_sum hper
      _ = ∑ q ∈ remainderModuli B N,
            |((((primeSequence N).filter (fun m => q ∣ m)).card : ℕ) : ℝ) -
                LeanLab.PNTPort.BVMax.liD (N : ℝ) / (q.totient : ℝ)| +
            (#(remainderModuli B N) : ℝ) * (2 / Real.log 2) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  -- (2) the mean value bound
  have stepB : ∑ q ∈ remainderModuli B N,
        |((((primeSequence N).filter (fun m => q ∣ m)).card : ℕ) : ℝ) -
            LeanLab.PNTPort.BVMax.liD (N : ℝ) / (q.totient : ℝ)| ≤ K * (N : ℝ) / Real.log N ^ 3 := by
    have hsub : remainderModuli B N ⊆
        (Finset.Icc 1 ⌊Real.sqrt N / Real.log N ^ B⌋₊).filter (fun d => Nat.Coprime N d) := by
      intro q hq
      rw [remainderModuli, Finset.mem_filter, Finset.mem_Icc] at hq
      obtain ⟨⟨hq1, hqQ⟩, -, hcop⟩ := hq
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hq1, by rw [hlevN] at hqQ; exact hqQ⟩, hcop.symm⟩
    have hb := hbv N (by omega)
    rw [hconv] at hb
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)).trans hb
  -- (3) at most `√N + 1` moduli, each costing `2 / log 2`
  have stepC : (#(remainderModuli B N) : ℝ) * (2 / Real.log 2) ≤
      (4 * K2 / Real.log 2) * (N : ℝ) / Real.log N ^ 3 := by
    have hsub : remainderModuli B N ⊆ Finset.Icc 1 Q := by
      intro q hq
      rw [remainderModuli, Finset.mem_filter, Finset.mem_Icc] at hq
      rw [Finset.mem_Icc]
      exact ⟨hq.1.1, by rw [hlevN] at *; exact hq.1.2⟩
    have h1 : #(remainderModuli B N) ≤ Q := by
      refine (Finset.card_le_card hsub).trans ?_
      rw [Nat.card_Icc]
      omega
    have hQle : (Q : ℝ) ≤ Real.sqrt N := by
      have h4 : (Q : ℝ) ≤ Real.sqrt N / Real.log N ^ B := Nat.floor_le (by positivity)
      have h5 : (1 : ℝ) ≤ Real.log N ^ B := by
        calc (1:ℝ) = (1:ℝ) ^ B := by simp
          _ ≤ Real.log N ^ B := Real.rpow_le_rpow (by norm_num) hlog1 hB.le
      calc (Q : ℝ) ≤ Real.sqrt N / Real.log N ^ B := h4
        _ ≤ Real.sqrt N / 1 := div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by norm_num) h5
        _ = Real.sqrt N := by norm_num
    have hcardM : (#(remainderModuli B N) : ℝ) ≤ Real.sqrt N :=
      (Nat.cast_le.mpr h1).trans hQle
    have hkey : (#(remainderModuli B N) : ℝ) * (2 / Real.log 2) ≤
        2 * (2 / Real.log 2) * Real.sqrt N := by
      have h6 := mul_le_mul_of_nonneg_right hcardM hC0
      have h7 : Real.sqrt N * (2 / Real.log 2) ≤ 2 * (2 / Real.log 2) * Real.sqrt N := by
        nlinarith [mul_nonneg hC0 (Real.sqrt_nonneg N)]
      linarith [h6, h7]
    have hlogb : Real.log N ^ 3 ≤ K2 * Real.sqrt N := by
      have h := hK2 (N : ℝ) hN2
      rwa [hconv] at h
    have hsqN : Real.sqrt N * Real.sqrt N = (N : ℝ) := by
      rw [← sq, Real.sq_sqrt hNpos.le]
    have h8 : Real.sqrt N ≤ K2 * ((N : ℝ) / Real.log N ^ 3) := by
      rw [show K2 * ((N : ℝ) / Real.log N ^ 3) = K2 * (N : ℝ) / Real.log N ^ 3 by ring,
        le_div_iff₀ hlog3]
      nlinarith [hlogb, Real.sqrt_nonneg N, hsqN]
    have hkey' : 2 * (2 / Real.log 2) * Real.sqrt N = (4 / Real.log 2) * Real.sqrt N := by ring
    calc (#(remainderModuli B N) : ℝ) * (2 / Real.log 2) ≤
          2 * (2 / Real.log 2) * Real.sqrt N := hkey
      _ = (4 / Real.log 2) * Real.sqrt N := hkey'
      _ ≤ (4 / Real.log 2) * (K2 * (N / Real.log N ^ 3)) := by
          apply mul_le_mul_of_nonneg_left h8 (by positivity)
      _ = (4 * K2 / Real.log 2) * (N : ℝ) / Real.log N ^ 3 := by ring
  have hsum := add_le_add stepB stepC
  have hKle : K ≤ max 0 K := le_max_right 0 K
  have hnn : (0 : ℝ) ≤ (N : ℝ) / Real.log N ^ 3 := by positivity
  calc rawRemainder B N
      ≤ K * (N : ℝ) / Real.log N ^ 3 + (4 * K2 / Real.log 2) * (N : ℝ) / Real.log N ^ 3 :=
        stepA.trans hsum
    _ = (K + 4 * K2 / Real.log 2) * (N : ℝ) / Real.log N ^ 3 := by ring
    _ ≤ (max 0 K + 4 * K2 / Real.log 2) * (N : ℝ) / Real.log N ^ 3 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [hKle, hnn]


/-- The exact sealed main0_lower statement follows from the two analytic pieces.
OPEN through linear_sieve_with_remainder and remainder_log_cubic.
This proof has no sorry of its own and calls neither original OPEN target. -/
theorem main0_lower_supplied (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 ≤ N →
        main0 f B N - η * Θ N ≤ sieveTerms N 0 := by
  intro η hη
  obtain ⟨K, hK, M, hM⟩ := li_density_scale_bounded
  obtain ⟨C, hC, hs⟩ := linear_sieve_with_remainder F f h
    (η / (3 * K)) (by positivity)
  obtain ⟨B, hB, D, hD, L, hL⟩ := remainder_log_cubic
  obtain ⟨J, hJ⟩ := hs B hB
  obtain ⟨T, hT⟩ := log_cubic_absorbed (C * D) (η / 3)
    (mul_nonneg hC hD) (by positivity)
  obtain ⟨U, hU⟩ := liMain0_error_absorbed F f h B (η / 3) (by positivity)
  refine ⟨B, hB, max M (max L (max J (max T U))), ?_⟩
  intro N hEven hN
  have hscale := hM N hEven (by omega)
  have hraw := mul_le_mul_of_nonneg_left (hL N hEven (by omega)) hC
  have hsmall := hT N (by omega)
  have hbudget : η / (3 * K) * (Wu04.li N * lowerDensity N) ≤
      η / 3 * Θ N := by
    calc
      _ ≤ η / (3 * K) * (K * Θ N) :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = _ := by field_simp
  have hremainder : C * rawRemainder B N ≤ η / 3 * Θ N := by
    calc
      _ ≤ C * (D * (N : ℝ) / log N ^ 3) := hraw
      _ = (C * D) * (N : ℝ) / log N ^ 3 := by ring
      _ ≤ _ := hsmall
  have hbound := hJ N hEven (by omega)
  have hli := le_trans (le_abs_self (main0 f B N - liMain0 f B N))
    (hU N hEven (by omega))
  linarith

end LeanLab.ChenDoubleSieve.Task363
