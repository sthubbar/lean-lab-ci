import LeanLab.ChenDoubleSieve.Decomp367e
import LeanLab.ChenDoubleSieve.Decomp363b
import LeanLab.ChenDoubleSieve.Decomp348c
import LeanLab.PNTPort.BVMax.PrimesUncond

/-!
Supply split for the finite F5 lower bound.
Source: https://arxiv.org/pdf/0705.1652, page 39 equation 10.5.
The discrepancy has not been absorbed into the sieve error.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task367
open Task275 Task348
open Wu04Functional (IsLinearSieve)

/-- The residual squarefree discrepancy moduli after fixing a prime pair.
The full progression modulus is the product of the pair and this modulus. -/
def pairModuli5 (B : ℝ) (N : ℕ) (p : ℕ × ℕ) : Finset ℕ :=
  (Finset.Icc 1 ⌊Task363.sieveLevel B N / (p.1 * p.2 : ℕ)⌋₊).filter
    (fun q => Squarefree q ∧ q.Coprime (N * (p.1 * p.2)))

/-- The absolute progression discrepancy summed over the actual F5 domain.
This contains neither a sieve function nor a sifted count. -/
def rawRemainder5 (B : ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ lowerPairs5 N, ∑ q ∈ pairModuli5 B N p,
    |(#((primeSequence N).filter (fun a => p.1 * p.2 * q ∣ a)) : ℝ) -
      Wu04.li N / (Nat.totient (p.1 * p.2 * q) : ℝ)|

/-- The absolute pair discrepancy is nonnegative. -/
theorem rawRemainder5_nonneg (B : ℝ) (N : ℕ) : 0 ≤ rawRemainder5 B N := by
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))

section Helpers367a

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
    Task363.sieveLevel B N = Real.sqrt N / Real.log N ^ B := by
  unfold Task363.sieveLevel
  rw [Real.sqrt_eq_rpow]

/-- `log 3 > 1`, in the form used below. -/
private theorem one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  have h := Real.log_three_near_10
  rw [abs_le] at h
  nlinarith [h.1]

end Helpers367a

section Domain367a

open LeanLab.PNTPort.BVMax

/-- The F5 lower pair domain exposes its primes, its coprimality and its power bounds. -/
private theorem lowerPairs5_facts {N : ℕ} {p : ℕ × ℕ} (hp : p ∈ lowerPairs5 N) :
    p.1.Prime ∧ p.2.Prime ∧ p.1.Coprime N ∧ p.2.Coprime N ∧ p.1 < p.2 ∧
      (N : ℝ) ^ kappa1 ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) < (N : ℝ) ^ kappa2 ∧
      (N : ℝ) ^ kappa2 ≤ (p.2 : ℝ) := by
  simp only [lowerPairs5, Wu08Sum.P2, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range] at hp
  have h1 : p.1.Prime := by tauto
  have h2 : p.2.Prime := by tauto
  have hc1 : p.1.Coprime N := by tauto
  have hc2 : p.2.Coprime N := by tauto
  have hlo : (N : ℝ) ^ kappa1 ≤ (p.1 : ℝ) := by tauto
  have hup : (p.1 : ℝ) < (N : ℝ) ^ kappa2 := by tauto
  have hmid : (N : ℝ) ^ kappa2 ≤ (p.2 : ℝ) := by tauto
  have hpos : (0 : ℝ) < (N : ℝ) ^ kappa2 :=
    Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < N)) kappa2
  have hltR : (p.1 : ℝ) < (p.2 : ℝ) := by linarith
  have hlt : p.1 < p.2 := by exact_mod_cast hltR
  exact ⟨h1, h2, hc1, hc2, hlt, hlo, hup, hmid⟩

/-- The sieving level never exceeds the square root of `N`. -/
private theorem sieveLevel_le_sqrt {B : ℝ} (hB : 0 < B) {N : ℕ} (hN : 3 ≤ N) :
    Task363.sieveLevel B N ≤ Real.sqrt N := by
  have hlog1 : 1 ≤ Real.log N :=
    one_le_log_three.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hN))
  have hpow : (1 : ℝ) ≤ Real.log N ^ B := by
    calc (1 : ℝ) = (1 : ℝ) ^ B := by simp
      _ ≤ Real.log N ^ B := Real.rpow_le_rpow (by norm_num) hlog1 hB.le
  have hlev : Task363.sieveLevel B N = Real.sqrt N / Real.log N ^ B := sieveLevel_eq B N
  rw [hlev]
  calc Real.sqrt N / Real.log N ^ B ≤ Real.sqrt N / 1 :=
        div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by norm_num) hpow
    _ = Real.sqrt N := by norm_num

/-- The full progression modulus of an F5 pair lies below the sieving level. -/
private theorem pairModuli5_mul_le {B : ℝ} {N : ℕ} {p : ℕ × ℕ} {q : ℕ}
    (hp : p ∈ lowerPairs5 N) (hq : q ∈ pairModuli5 B N p) :
    ((p.1 * p.2 * q : ℕ) : ℝ) ≤ Task363.sieveLevel B N := by
  obtain ⟨hp1, hp2, -, -, -, -, -, -⟩ := lowerPairs5_facts hp
  simp only [pairModuli5, Finset.mem_filter, Finset.mem_Icc] at hq
  have hqle : q ≤ ⌊Task363.sieveLevel B N / (p.1 * p.2 : ℕ)⌋₊ := hq.1.2
  have hlevnn : (0 : ℝ) ≤ Task363.sieveLevel B N := by
    rw [sieveLevel_eq]; positivity
  have hden : (0 : ℝ) < (p.1 : ℝ) * p.2 := by
    have h1 : (2 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast hp1.two_le
    have h2 : (2 : ℝ) ≤ (p.2 : ℝ) := by exact_mod_cast hp2.two_le
    nlinarith
  have hnn : (0 : ℝ) ≤ Task363.sieveLevel B N / ((p.1 : ℝ) * p.2) := div_nonneg hlevnn hden.le
  have hfl := Nat.floor_le hnn
  have hqle' : (q : ℝ) ≤ Task363.sieveLevel B N / ((p.1 : ℝ) * p.2) := by
    refine le_trans ?_ hfl
    exact_mod_cast hqle
  have hcast : ((p.1 * p.2 * q : ℕ) : ℝ) = (p.1 : ℝ) * p.2 * q := by push_cast; ring
  rw [hcast]
  calc (p.1 : ℝ) * p.2 * q ≤ (p.1 : ℝ) * p.2 * (Task363.sieveLevel B N / ((p.1 : ℝ) * p.2)) :=
        mul_le_mul_of_nonneg_left hqle' hden.le
    _ = Task363.sieveLevel B N := mul_div_cancel₀ _ hden.ne'

/-- The full progression modulus of an F5 pair is coprime to `N`. -/
private theorem coprime_mul_N {B : ℝ} {N : ℕ} {p : ℕ × ℕ} {q : ℕ}
    (hp : p ∈ lowerPairs5 N) (hq : q ∈ pairModuli5 B N p) :
    (p.1 * p.2 * q).Coprime N := by
  obtain ⟨hp1, hp2, hc1, hc2, hlt, -, -, -⟩ := lowerPairs5_facts hp
  simp only [pairModuli5, Finset.mem_filter] at hq
  have hqcop : q.Coprime (N * (p.1 * p.2)) := hq.2.2
  have hqN : q.Coprime N :=
    Nat.Coprime.coprime_dvd_right (n := N) (m := N * (p.1 * p.2)) ⟨p.1 * p.2, rfl⟩ hqcop
  have h12 : p.1.Coprime p.2 :=
    (Nat.coprime_primes hp1 hp2).2 (by omega)
  have hpp : (p.1 * p.2).Coprime N := hc1.mul_left hc2
  have hres : ((p.1 * p.2) * q).Coprime N := hpp.mul_left hqN
  simpa only [mul_assoc] using hres

/-- One progression term: replacing `li` by the discrete `liD` costs two over `log 2`. -/
private theorem term_li_le {N m : ℕ} (hN : 2 ≤ N) (hm : 1 ≤ m) :
    |((#((primeSequence N).filter (fun a => m ∣ a)) : ℝ) -
        Wu04.li N / (Nat.totient m : ℝ))| ≤
      |((#((primeSequence N).filter (fun a => m ∣ a)) : ℝ) -
        liD (N : ℝ) / (Nat.totient m : ℝ))| + 2 / Real.log 2 := by
  have hφpos : (0 : ℝ) < (Nat.totient m : ℝ) := by
    have h := Nat.totient_pos.2 (by omega : 0 < m)
    exact_mod_cast h
  have hφ1 : (1 : ℝ) ≤ (Nat.totient m : ℝ) := by
    have h := Nat.totient_pos.2 (by omega : 0 < m)
    exact_mod_cast h
  have hli := abs_liD_sub_li N hN
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hc0 : (0 : ℝ) ≤ 2 / Real.log 2 := by positivity
  have hstep : |liD (N : ℝ) / (Nat.totient m : ℝ) - Wu04.li N / (Nat.totient m : ℝ)| ≤
      2 / Real.log 2 := by
    have heq : liD (N : ℝ) / (Nat.totient m : ℝ) - Wu04.li N / (Nat.totient m : ℝ) =
        (liD (N : ℝ) - Wu04.li N) / (Nat.totient m : ℝ) := by ring
    rw [heq, abs_div, abs_of_pos hφpos]
    calc |liD (N : ℝ) - Wu04.li N| / (Nat.totient m : ℝ) ≤
          (2 / Real.log 2) / (Nat.totient m : ℝ) := by gcongr
      _ ≤ (2 / Real.log 2) / 1 := div_le_div_of_nonneg_left hc0 (by norm_num) hφ1
      _ = 2 / Real.log 2 := by norm_num
  calc |((#((primeSequence N).filter (fun a => m ∣ a)) : ℝ) -
        Wu04.li N / (Nat.totient m : ℝ))|
      ≤ |((#((primeSequence N).filter (fun a => m ∣ a)) : ℝ) -
            liD (N : ℝ) / (Nat.totient m : ℝ))| +
          |liD (N : ℝ) / (Nat.totient m : ℝ) - Wu04.li N / (Nat.totient m : ℝ)| := by
        simpa [Real.dist_eq] using dist_triangle
          (((#((primeSequence N).filter (fun a => m ∣ a)) : ℕ)) : ℝ)
          (liD (N : ℝ) / (Nat.totient m : ℝ)) (Wu04.li N / (Nat.totient m : ℝ))
    _ ≤ _ := by linarith

end Domain367a

section Count367a

/-- A power of `c` is at most a product of `card` many terms each at least `c`. -/
private theorem pow_card_le_prod {c : ℝ} (hc : 0 ≤ c) (s : Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ p ∈ s, c ≤ f p) (h0 : ∀ p ∈ s, 0 ≤ f p) :
    c ^ s.card ≤ ∏ p ∈ s, f p := by
  classical
  revert hf h0
  induction s using Finset.induction_on with
  | empty => intro _ _; simp
  | insert a s ha ih =>
      intro hf h0
      rw [Finset.card_insert_of_notMem ha, Finset.prod_insert ha, pow_succ]
      have ih' := ih (fun p hp => hf p (Finset.mem_insert_of_mem hp))
        (fun p hp => h0 p (Finset.mem_insert_of_mem hp))
      have hfa : c ≤ f a := hf a (Finset.mem_insert_self a s)
      have hprod0 : (0 : ℝ) ≤ ∏ p ∈ s, f p :=
        Finset.prod_nonneg (fun p hp => h0 p (Finset.mem_insert_of_mem hp))
      calc c ^ s.card * c ≤ (∏ p ∈ s, f p) * c := mul_le_mul_of_nonneg_right ih' hc
        _ ≤ (∏ p ∈ s, f p) * f a := mul_le_mul_of_nonneg_left hfa hprod0
        _ = f a * ∏ p ∈ s, f p := by ring

/-- At most six primes of the F5 lower band divide a nonzero modulus below `√N`. -/
private theorem card_band_primes_le {N m : ℕ} (hN : 1 < N) (hm0 : 0 < m)
    (hm : (m : ℝ) ≤ Real.sqrt N) :
    #((m.primeFactors).filter (fun p : ℕ => (N : ℝ) ^ kappa1 ≤ (p : ℝ))) ≤ 6 := by
  classical
  set P : Finset ℕ := (m.primeFactors).filter (fun p : ℕ => (N : ℝ) ^ kappa1 ≤ (p : ℝ)) with hP
  have hNR : (1 : ℝ) < N := by exact_mod_cast hN
  have hc0 : (0 : ℝ) ≤ (N : ℝ) ^ kappa1 :=
    (Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < N)) kappa1).le
  have hsub : P ⊆ m.primeFactors := by rw [hP]; exact Finset.filter_subset _ _
  have hdvd : ∏ p ∈ P, p ∣ m := by
    have h1 : ∏ p ∈ P, p ∣ ∏ p ∈ m.primeFactors, p :=
      Finset.prod_dvd_prod_of_subset P m.primeFactors (fun p => p) hsub
    exact h1.trans (Nat.prod_primeFactors_dvd m)
  have hprod_le : ((∏ p ∈ P, p : ℕ) : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast Nat.le_of_dvd hm0 hdvd
  have hlow : ((N : ℝ) ^ kappa1) ^ P.card ≤ (∏ p ∈ P, (p : ℝ)) := by
    refine pow_card_le_prod hc0 P (fun p => (p : ℝ)) ?_ ?_
    · intro p hp
      rw [hP, Finset.mem_filter] at hp
      exact hp.2
    · intro p hp; positivity
  rw [Real.sqrt_eq_rpow] at hm
  have hmain : (N : ℝ) ^ (kappa1 * (P.card : ℝ)) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
    have he : (N : ℝ) ^ (kappa1 * (P.card : ℝ)) = ((N : ℝ) ^ kappa1) ^ P.card := by
      rw [Real.rpow_mul (le_of_lt (by exact_mod_cast (by omega : 0 < N))), Real.rpow_natCast]
    rw [he]
    calc ((N : ℝ) ^ kappa1) ^ P.card ≤ (∏ p ∈ P, (p : ℝ)) := hlow
      _ = ((∏ p ∈ P, p : ℕ) : ℝ) := (Nat.cast_prod _ _).symm
      _ ≤ (m : ℝ) := hprod_le
      _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) := hm
  have hexp : kappa1 * (P.card : ℝ) ≤ 1 / 2 := (Real.rpow_le_rpow_left_iff hNR).1 hmain
  rw [show kappa1 = (1 : ℝ) / 12 from by norm_num [kappa1]] at hexp
  have hk : (P.card : ℝ) ≤ 6 := by nlinarith
  exact_mod_cast hk

/-- Each progression modulus comes from at most thirty six F5 pair and modulus choices. -/
private theorem card_fiber_le {B : ℝ} (hB : 0 < B) {N : ℕ} (hN : 3 ≤ N) (m : ℕ) :
    #(((lowerPairs5 N).sigma (fun p => pairModuli5 B N p)).filter
        (fun x => x.1.1 * x.1.2 * x.2 = m)) ≤ 36 := by
  classical
  set S := (lowerPairs5 N).sigma (fun p => pairModuli5 B N p) with hS
  set F := S.filter (fun x => x.1.1 * x.1.2 * x.2 = m) with hF
  rcases Finset.eq_empty_or_nonempty F with hemp | ⟨x0, hx0⟩
  · rw [hemp]; simp
  have hx0S : x0 ∈ S := (Finset.mem_filter.1 hx0).1
  have hx0m : x0.1.1 * x0.1.2 * x0.2 = m := (Finset.mem_filter.1 hx0).2
  obtain ⟨hp0, hq0⟩ := Finset.mem_sigma.1 hx0S
  obtain ⟨hp01, hp02, -, -, -, -, -, -⟩ := lowerPairs5_facts hp0
  have hq01 : 1 ≤ x0.2 := by
    simp only [pairModuli5, Finset.mem_filter, Finset.mem_Icc] at hq0
    exact hq0.1.1
  have hmpos : 0 < m := by
    rw [← hx0m]
    have h1 : 2 ≤ x0.1.1 := hp01.two_le
    have h2 : 2 ≤ x0.1.2 := hp02.two_le
    have h3 : 1 ≤ x0.2 := hq01
    positivity
  have hmle : (m : ℝ) ≤ Real.sqrt N := by
    rw [← hx0m]
    have hq0' : x0.2 ∈ pairModuli5 B N x0.1 := hq0
    exact (pairModuli5_mul_le hp0 hq0').trans (sieveLevel_le_sqrt hB hN)
  set P : Finset ℕ := (m.primeFactors).filter (fun p : ℕ => (N : ℝ) ^ kappa1 ≤ (p : ℝ)) with hP
  have hPcard : #P ≤ 6 := card_band_primes_le (by omega) hmpos hmle
  have hmaps : ∀ x ∈ F, (x.1.1, x.1.2) ∈ P ×ˢ P := by
    intro x hx
    obtain ⟨hxS, hxm⟩ := Finset.mem_filter.1 hx
    obtain ⟨hp, hq⟩ := Finset.mem_sigma.1 hxS
    obtain ⟨hp1, hp2, -, -, hlt, hlo, hup, hmid⟩ := lowerPairs5_facts hp
    have hxq1 : 1 ≤ x.2 := by
      simp only [pairModuli5, Finset.mem_filter, Finset.mem_Icc] at hq
      exact hq.1.1
    have hxpos : 0 < m := by
      rw [← hxm]
      have h1 : 2 ≤ x.1.1 := hp1.two_le
      have h2 : 2 ≤ x.1.2 := hp2.two_le
      have h3 : 1 ≤ x.2 := hxq1
      positivity
    refine Finset.mem_product.2 ⟨?_, ?_⟩
    · rw [hP, Finset.mem_filter]
      refine ⟨Nat.mem_primeFactors.2 ⟨hp1, ?_, hxpos.ne'⟩, ?_⟩
      · exact ⟨x.1.2 * x.2, by rw [← hxm]; ring⟩
      · simpa using hlo
    · rw [hP, Finset.mem_filter]
      refine ⟨Nat.mem_primeFactors.2 ⟨hp2, ?_, hxpos.ne'⟩, ?_⟩
      · exact ⟨x.1.1 * x.2, by rw [← hxm]; ring⟩
      · have hk : (N : ℝ) ^ kappa1 ≤ (N : ℝ) ^ kappa2 :=
          (Real.rpow_le_rpow_left_iff (by exact_mod_cast (by omega : 1 < N))).2
            (by norm_num [kappa1, kappa2])
        exact hk.trans hmid
  have hinj : ∀ x ∈ F, ∀ y ∈ F, (x.1.1, x.1.2) = (y.1.1, y.1.2) → x = y := by
    intro x hx y hy heq
    have h1 : x.1.1 = y.1.1 := congrArg Prod.fst heq
    have h2 : x.1.2 = y.1.2 := congrArg Prod.snd heq
    have hxm : x.1.1 * x.1.2 * x.2 = m := (Finset.mem_filter.1 hx).2
    have hym : y.1.1 * y.1.2 * y.2 = m := (Finset.mem_filter.1 hy).2
    have hyS : y.1 ∈ lowerPairs5 N := (Finset.mem_sigma.1 (Finset.mem_filter.1 hy).1).1
    obtain ⟨hpy1, hpy2, -, -, -, -, -, -⟩ := lowerPairs5_facts hyS
    have hpos : 0 < y.1.1 * y.1.2 := by
      have h3 : 2 ≤ y.1.1 := hpy1.two_le
      have h4 : 2 ≤ y.1.2 := hpy2.two_le
      positivity
    have hmul : y.1.1 * y.1.2 * x.2 = y.1.1 * y.1.2 * y.2 := by
      rw [h1, h2] at hxm
      rw [hxm, hym]
    have hq : x.2 = y.2 := Nat.mul_left_cancel hpos hmul
    exact Sigma.ext (Prod.ext h1 h2) (heq_of_eq hq)
  have hcard : #F ≤ #(P ×ˢ P) :=
    Finset.card_le_card_of_injOn (fun x => (x.1.1, x.1.2)) hmaps hinj
  rw [Finset.card_product] at hcard
  nlinarith [hPcard]

end Count367a

section Sum367a

/-- A sum over the F5 pair and modulus domain of any nonnegative function of the full modulus
is at most thirty six times the sum over the moduli that occur. -/
private theorem sum_domain_le {B : ℝ} (hB : 0 < B) {N : ℕ} (hN : 3 ≤ N)
    (g : ℕ → ℝ) (hg : ∀ m, 0 ≤ g m) :
    ∑ x ∈ (lowerPairs5 N).sigma (fun p => pairModuli5 B N p),
        g (x.1.1 * x.1.2 * x.2) ≤
      36 * ∑ m ∈ ((lowerPairs5 N).sigma (fun p => pairModuli5 B N p)).image
          (fun x => x.1.1 * x.1.2 * x.2), g m := by
  classical
  have hfib := Finset.sum_fiberwise_of_maps_to'
    (s := (lowerPairs5 N).sigma (fun p => pairModuli5 B N p))
    (t := ((lowerPairs5 N).sigma (fun p => pairModuli5 B N p)).image
      (fun x => x.1.1 * x.1.2 * x.2))
    (g := fun x => x.1.1 * x.1.2 * x.2)
    (fun _ hx => Finset.mem_image_of_mem _ hx) (f := g)
  rw [← hfib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m hm
  rw [Finset.sum_const, nsmul_eq_mul]
  have hc : ((#(((lowerPairs5 N).sigma (fun p => pairModuli5 B N p)).filter
      (fun x => x.1.1 * x.1.2 * x.2 = m)) : ℕ) : ℝ) ≤ 36 := by
    exact_mod_cast card_fiber_le hB hN m
  nlinarith [hg m, hc]

end Sum367a

/-- LEAF. Wu 2004 page 39 equation 10.5, lower sieve part of the
application of Lemma 2.2, as in the preceding page 38 argument.
Retain the arithmetic progression discrepancy with its sieve constant.
Retain the li main term and the total reciprocal totient mass.
Only the local density scale is normalized into Theta.
Neither the li replacement nor the mean value bound has been applied. -/
theorem pair_linear_sieve_with_remainder (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ B : ℝ, 0 < B → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
        liMain5 f B N - δ * Θ N * lowerTotientMass5 N -
          C * rawRemainder5 B N ≤ sieveTerms N 5 := by
  sorry

/-- LEAF. Wu 2004 page 39 equation 10.5, mean value part of the
application of Lemma 2.3, as in the preceding error display on that page.
This bound contains no sifted count and no linear sieve function. -/
theorem pair_remainder_log_cubic : ∃ B : ℝ, 0 < B ∧ ∃ D : ℝ, 0 ≤ D ∧
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      rawRemainder5 B N ≤ D * (N : ℝ) / log N ^ 3 := by
  classical
  obtain ⟨B, hB, K, hKbv⟩ := bvPrimeSequence 3 (by norm_num)
  obtain ⟨K2, hK2pos, hK2⟩ := LeanLab.PNTPort.BV.log_rpow_le_sqrt 3
  obtain ⟨Kp, hKppos, Mp, hKp⟩ := fullPairs5_mass_bounded
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hc0 : (0 : ℝ) ≤ 2 / Real.log 2 := by positivity
  refine ⟨B, hB, 36 * max 0 K + (Kp * K2) * (2 / Real.log 2), by positivity,
    max 3 (max Mp 1), ?_⟩
  intro N hEven hN
  have hN3 : 3 ≤ N := le_trans (le_max_left 3 (max Mp 1)) hN
  have hNMp : Mp ≤ N :=
    le_trans (le_trans (le_max_left Mp 1) (le_max_right 3 (max Mp 1))) hN
  have hN2R : (2 : ℝ) ≤ N := by exact_mod_cast (by omega : 2 ≤ N)
  have hNpos : (0 : ℝ) < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  have hlog3 : 0 < Real.log N ^ 3 := by positivity
  have hNnn : (0 : ℝ) ≤ (N : ℝ) / Real.log N ^ 3 := by positivity
  set S := (lowerPairs5 N).sigma (fun p => pairModuli5 B N p) with hS
  set T := S.image (fun x => x.1.1 * x.1.2 * x.2) with hT
  set Xd : ℕ → ℝ := fun m => |((#((primeSequence N).filter (fun a => m ∣ a)) : ℕ) : ℝ) -
      LeanLab.PNTPort.BVMax.liD (N : ℝ) / (Nat.totient m : ℝ)| with hXd
  have hconv : Real.log (N : ℝ) ^ (3 : ℝ) = Real.log N ^ 3 := Real.rpow_natCast _ _
  have hterm : ∀ p ∈ lowerPairs5 N, ∀ q ∈ pairModuli5 B N p,
      |((#((primeSequence N).filter (fun a => p.1 * p.2 * q ∣ a)) : ℕ) : ℝ) -
          Wu04.li N / (Nat.totient (p.1 * p.2 * q) : ℝ)| ≤
        Xd (p.1 * p.2 * q) + 2 / Real.log 2 := by
    intro p hp q hq
    obtain ⟨hp1, hp2, -, -, -, -, -, -⟩ := lowerPairs5_facts hp
    have hq1 : 1 ≤ q := by
      simp only [pairModuli5, Finset.mem_filter, Finset.mem_Icc] at hq
      exact hq.1.1
    have hm1 : 1 ≤ p.1 * p.2 * q := by
      have h2 : 0 < p.1 := hp1.pos
      have h3 : 0 < p.2 := hp2.pos
      have h4 : 0 < q := by omega
      have h5 : 0 < p.1 * p.2 * q := by positivity
      omega
    rw [hXd]
    exact term_li_le (by omega) hm1
  -- split the constant term
  have hsplit : ∀ p ∈ lowerPairs5 N,
      ∑ q ∈ pairModuli5 B N p, (Xd (p.1 * p.2 * q) + 2 / Real.log 2) =
        (∑ q ∈ pairModuli5 B N p, Xd (p.1 * p.2 * q)) +
          (#(pairModuli5 B N p) : ℝ) * (2 / Real.log 2) := by
    intro p hp
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have hstep2 : ∑ p ∈ lowerPairs5 N, ∑ q ∈ pairModuli5 B N p,
        (Xd (p.1 * p.2 * q) + 2 / Real.log 2) =
      (∑ p ∈ lowerPairs5 N, ∑ q ∈ pairModuli5 B N p, Xd (p.1 * p.2 * q)) +
        (#S : ℝ) * (2 / Real.log 2) := by
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
    congr 1
    rw [hS, Finset.card_sigma]
    push_cast
    rw [← Finset.sum_mul]
  have hstep3 : (∑ p ∈ lowerPairs5 N, ∑ q ∈ pairModuli5 B N p, Xd (p.1 * p.2 * q)) ≤
      36 * ∑ m ∈ T, Xd m := by
    have h := sum_domain_le hB hN3 Xd (fun m => by simp only [hXd]; positivity)
    calc ∑ p ∈ lowerPairs5 N, ∑ q ∈ pairModuli5 B N p, Xd (p.1 * p.2 * q)
        = ∑ x ∈ S, Xd (x.1.1 * x.1.2 * x.2) := by
          rw [hS]
          exact (Finset.sum_sigma (lowerPairs5 N) (fun p => pairModuli5 B N p)
            (fun x => Xd (x.1.1 * x.1.2 * x.2))).symm
      _ = ∑ x ∈ (lowerPairs5 N).sigma (fun p => pairModuli5 B N p),
            Xd (x.1.1 * x.1.2 * x.2) := by rw [hS]
      _ ≤ 36 * ∑ m ∈ ((lowerPairs5 N).sigma (fun p => pairModuli5 B N p)).image
            (fun x => x.1.1 * x.1.2 * x.2), Xd m := h
      _ = 36 * ∑ m ∈ T, Xd m := by rw [hT, hS]
  have hTsub : T ⊆ (Finset.Icc 1 ⌊Real.sqrt N / Real.log N ^ B⌋₊).filter
      (fun d => Nat.Coprime N d) := by
    intro m hm
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hm
    have hxS : x ∈ (lowerPairs5 N).sigma (fun p => pairModuli5 B N p) := by
      rw [← hS]; exact hx
    obtain ⟨hp, hq⟩ := Finset.mem_sigma.1 hxS
    obtain ⟨hp1, hp2, -, -, -, -, -, -⟩ := lowerPairs5_facts hp
    have hq1 : 1 ≤ x.2 := by
      simp only [pairModuli5, Finset.mem_filter, Finset.mem_Icc] at hq
      exact hq.1.1
    refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨?_, ?_⟩, ?_⟩
    · have h2 : 0 < x.1.1 := hp1.pos
      have h3 : 0 < x.1.2 := hp2.pos
      have h4 : 0 < x.2 := by omega
      have h5 : 0 < x.1.1 * x.1.2 * x.2 := by positivity
      omega
    · have hmm : ((x.1.1 * x.1.2 * x.2 : ℕ) : ℝ) ≤ Task363.sieveLevel B N :=
        pairModuli5_mul_le hp hq
      have hfl : x.1.1 * x.1.2 * x.2 ≤ ⌊Task363.sieveLevel B N⌋₊ := Nat.le_floor hmm
      rwa [sieveLevel_eq] at hfl
    · exact (coprime_mul_N hp hq).symm
  have hBV : ∑ m ∈ T, Xd m ≤ K * (N : ℝ) / Real.log N ^ 3 := by
    have h1 : ∑ m ∈ T, Xd m ≤
        ∑ m ∈ (Finset.Icc 1 ⌊Real.sqrt N / Real.log N ^ B⌋₊).filter
          (fun d => Nat.Coprime N d), Xd m :=
      Finset.sum_le_sum_of_subset_of_nonneg hTsub (fun _ _ _ => abs_nonneg _)
    have h2 := hKbv N (by omega : 2 ≤ N)
    rw [hconv] at h2
    simp only [hXd] at h1 h2 ⊢
    exact h1.trans h2
  have hmass : pairMass (lowerPairs5 N) ≤ Kp := by
    refine (pairMass_mono ?_).trans (hKp N hNMp)
    rw [lowerPairs5_eq_filter]
    exact Finset.filter_subset _ _
  have hScard : (#S : ℝ) ≤ Kp * Real.sqrt N := by
    have hcard : (#S : ℝ) = ∑ p ∈ lowerPairs5 N, (#(pairModuli5 B N p) : ℝ) := by
      rw [hS, Finset.card_sigma, Nat.cast_sum]
    rw [hcard]
    have hbound : ∀ p ∈ lowerPairs5 N, (#(pairModuli5 B N p) : ℝ) ≤
        Task363.sieveLevel B N / ((p.1 : ℝ) * p.2) := by
      intro p hp
      obtain ⟨hp1, hp2, -, -, -, -, -, -⟩ := lowerPairs5_facts hp
      have hsub : pairModuli5 B N p ⊆
          Finset.Icc 1 ⌊Task363.sieveLevel B N / (p.1 * p.2 : ℕ)⌋₊ := Finset.filter_subset _ _
      have hcard' : #(pairModuli5 B N p) ≤ ⌊Task363.sieveLevel B N / (p.1 * p.2 : ℕ)⌋₊ := by
        refine (Finset.card_le_card hsub).trans ?_
        rw [Nat.card_Icc]; omega
      have hden : (0 : ℝ) < (p.1 : ℝ) * p.2 := by
        have h1 : 2 ≤ (p.1 : ℝ) := by exact_mod_cast hp1.two_le
        have h2 : 2 ≤ (p.2 : ℝ) := by exact_mod_cast hp2.two_le
        nlinarith
      have hlevnn : (0 : ℝ) ≤ Task363.sieveLevel B N := by
        rw [sieveLevel_eq]; positivity
      calc (#(pairModuli5 B N p) : ℝ) ≤
            ((⌊Task363.sieveLevel B N / (p.1 * p.2 : ℕ)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hcard'
        _ ≤ Task363.sieveLevel B N / ((p.1 : ℝ) * p.2) := by
            have h := Nat.floor_le (div_nonneg hlevnn hden.le)
            simpa only [Nat.cast_mul] using h
    calc ∑ p ∈ lowerPairs5 N, (#(pairModuli5 B N p) : ℝ)
        ≤ ∑ p ∈ lowerPairs5 N, Task363.sieveLevel B N / ((p.1 : ℝ) * p.2) :=
          Finset.sum_le_sum hbound
      _ = Task363.sieveLevel B N * pairMass (lowerPairs5 N) := by
          rw [pairMass, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp; ring
      _ ≤ Real.sqrt N * Kp := by
          have h1 := sieveLevel_le_sqrt (B := B) hB hN3
          have h2 : (0 : ℝ) ≤ Task363.sieveLevel B N := by rw [sieveLevel_eq]; positivity
          nlinarith
      _ = Kp * Real.sqrt N := by ring
  have hlogb : Real.log N ^ (3 : ℝ) ≤ K2 * Real.sqrt N := hK2 (N : ℝ) hN2R
  have h8 : Real.sqrt N ≤ K2 * ((N : ℝ) / Real.log N ^ 3) := by
    rw [hconv] at hlogb
    rw [show K2 * ((N : ℝ) / Real.log N ^ 3) = K2 * (N : ℝ) / Real.log N ^ 3 by ring,
      le_div_iff₀ hlog3]
    have hsq : Real.sqrt N * Real.sqrt N = (N : ℝ) := by
      rw [← sq, Real.sq_sqrt hNpos.le]
    nlinarith [hlogb, Real.sqrt_nonneg N, hsq]
  have hSterm : (#S : ℝ) * (2 / Real.log 2) ≤
      ((Kp * K2) * (2 / Real.log 2)) * (N : ℝ) / Real.log N ^ 3 := by
    have h1 : (#S : ℝ) * (2 / Real.log 2) ≤ (Kp * Real.sqrt N) * (2 / Real.log 2) :=
      mul_le_mul_of_nonneg_right hScard hc0
    have h2 : (Kp * Real.sqrt N) * (2 / Real.log 2) ≤
        (Kp * (K2 * ((N : ℝ) / Real.log N ^ 3))) * (2 / Real.log 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h8 hKppos.le) hc0
    calc (#S : ℝ) * (2 / Real.log 2) ≤ (Kp * Real.sqrt N) * (2 / Real.log 2) := h1
      _ ≤ (Kp * (K2 * ((N : ℝ) / Real.log N ^ 3))) * (2 / Real.log 2) := h2
      _ = ((Kp * K2) * (2 / Real.log 2)) * (N : ℝ) / Real.log N ^ 3 := by ring
  have hKle : K ≤ max 0 K := le_max_right 0 K
  have h36 : 36 * (∑ m ∈ T, Xd m) ≤ 36 * (max 0 K * ((N : ℝ) / Real.log N ^ 3)) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    calc ∑ m ∈ T, Xd m ≤ K * ((N : ℝ) / Real.log N ^ 3) := by
          rw [show K * ((N : ℝ) / Real.log N ^ 3) = K * (N : ℝ) / Real.log N ^ 3 by ring]
          exact hBV
      _ ≤ max 0 K * ((N : ℝ) / Real.log N ^ 3) :=
          mul_le_mul_of_nonneg_right hKle hNnn
  calc rawRemainder5 B N
      = ∑ p ∈ lowerPairs5 N, ∑ q ∈ pairModuli5 B N p,
          |((#((primeSequence N).filter (fun a => p.1 * p.2 * q ∣ a)) : ℕ) : ℝ) -
            Wu04.li N / (Nat.totient (p.1 * p.2 * q) : ℝ)| := rfl
    _ ≤ ∑ p ∈ lowerPairs5 N, ∑ q ∈ pairModuli5 B N p,
          (Xd (p.1 * p.2 * q) + 2 / Real.log 2) :=
        Finset.sum_le_sum (fun p hp => Finset.sum_le_sum (fun q hq => hterm p hp q hq))
    _ = (∑ p ∈ lowerPairs5 N, ∑ q ∈ pairModuli5 B N p, Xd (p.1 * p.2 * q)) +
          (#S : ℝ) * (2 / Real.log 2) := hstep2
    _ ≤ 36 * (max 0 K * ((N : ℝ) / Real.log N ^ 3)) +
          ((Kp * K2) * (2 / Real.log 2)) * (N : ℝ) / Real.log N ^ 3 := by
        linarith [hstep3, h36, hSterm]
    _ = (36 * max 0 K + (Kp * K2) * (2 / Real.log 2)) * (N : ℝ) / Real.log N ^ 3 := by ring

/-- The exact sealed main5_lower target follows from the two smaller inputs.
OPEN through the lower sieve construction and the pair mean value estimate.
This assembly calls neither original OPEN theorem. -/
theorem main5_lower_supplied (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 ≤ N →
        main5 f B N - η * Θ N ≤ sieveTerms N 5 := by
  intro η hη
  obtain ⟨K, hK, M, hM⟩ := lowerTotientMass5_bounded
  obtain ⟨C, hC, hs⟩ := pair_linear_sieve_with_remainder F f h
    (η / (3 * K)) (by positivity)
  obtain ⟨B, hB, D, hD, L, hL⟩ := pair_remainder_log_cubic
  obtain ⟨J, hJ⟩ := hs B hB
  obtain ⟨T, hT⟩ := Task363.log_cubic_absorbed (C * D) (η / 3)
    (mul_nonneg hC hD) (by positivity)
  obtain ⟨U, hU⟩ := liMain5_error_absorbed F f h B hB (η / 3) (by positivity)
  refine ⟨B, hB, max 2 (max M (max L (max J (max T U)))), ?_⟩
  intro N hEven hN
  have ht : 0 < Θ N := Θ_pos (by omega)
  have hbudget : η / (3 * K) * Θ N * lowerTotientMass5 N ≤ η / 3 * Θ N := by
    calc
      _ ≤ η / (3 * K) * Θ N * K :=
        mul_le_mul_of_nonneg_left (hM N (by omega)) (by positivity)
      _ = _ := by field_simp
  have hraw := mul_le_mul_of_nonneg_left (hL N hEven (by omega)) hC
  have hsmall := hT N (by omega)
  have heq : C * (D * (N : ℝ) / log N ^ 3) =
      (C * D) * (N : ℝ) / log N ^ 3 := by ring
  rw [heq] at hraw
  have hbound := hJ N hEven (by omega)
  have hli := le_trans (le_abs_self (main5 f B N - liMain5 f B N))
    (hU N hEven (by omega))
  linarith

end LeanLab.ChenDoubleSieve.Task367
