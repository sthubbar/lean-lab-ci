/- AI wrote this Lean code for CODEX task233.
Unchanged Lemmas 12 and 13 helpers moved from DecompC169b for reuse.
Journal pp. 1229 to 1231. Goldbach is open. -/
import LeanLab.BS2022GRH.ModelC233
import LeanLab.BS2022GRH.ProgressionC169
import LeanLab.BS2022GRH.CoefficientsC169
import LeanLab.BS2022GRH.PaperInputs148
import LeanLab.BS2022GRH.RangeCheck13375

namespace LeanLab.BS2022GRH.DecompC169b
open Real Finset Classical ChenThresholdGRH DecompC169a
noncomputable section

/-- The squarefree modulus count for any subset, CONDITIONAL ON Lemma 5, p. 1216. -/
theorem squarefree_count_le (hMu : PaperInputs148.Lemma5MuJ) (s : Finset ℕ) (H : ℝ)
    (hH : 1 ≤ H) (hs : ∀ d ∈ s, Squarefree d ∧ 1 ≤ d ∧ (d : ℝ) ≤ H) :
    (s.card : ℝ) ≤ Lemma5Coeffs138.mMu H * H := by
  apply le_trans _ (hMu H hH)
  exact_mod_cast card_le_card (show s ⊆ (Icc 1 ⌊H⌋₊).filter Squarefree from by
    intro d hd
    obtain ⟨hsq, hd1, hdH⟩ := hs d hd
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hd1, Nat.le_floor hdH⟩, hsq⟩)


/-- The progression with d dividing n minus p is the usual class of n, p. 1229. -/
theorem progressionPrimes_eq (n d : ℕ) :
    ProgressionC169.progressionPrimes n d =
      (range (n + 1)).filter (fun p => p.Prime ∧ p % d = n % d) := by
  apply filter_congr
  intro p hp
  have hpn : p ≤ n := by have := mem_range.mp hp; omega
  exact and_congr_right fun _ => (Nat.modEq_iff_dvd' hpn).symm


/-- The progression error vanishes at modulus one, p. 1230. -/
theorem progressionError_one (n : ℕ) : ProgressionC169.progressionError n 1 = 0 := by
  simp [ProgressionC169.progressionError, ProgressionC169.progressionPrimes]


/-- The totient denominator contributes at most one half for d at least three, p. 1230. -/
theorem half_totient {d : ℕ} (hd : 3 ≤ d) : (2 : ℝ) ≤ d.totient := by
  have hφ : 2 ≤ d.totient := by
    by_contra h
    have hdiv := Nat.dvd_two_of_totient_le_one (by omega : 0 < d) (by omega)
    have := Nat.le_of_dvd (by norm_num : 0 < 2) hdiv
    omega
  exact_mod_cast hφ


/-- Lemma 12 pointwise estimate, CONDITIONAL ON Lemmas 1 and 3 and GRH, p. 1230. -/
theorem progression_error_le (h1 : PaperInputs148.Lemma1J) (h3 : Lemma3J)
    (hG : GRH) (n d : ℕ) (X : ℝ) (hX : 2657 ≤ X) (hn : X ≤ (n : ℝ))
    (hd : 3 ≤ d) (hdn : (d : ℝ) ≤ √(n : ℝ)) (hc : Nat.Coprime n d) :
    |ProgressionC169.progressionError n d| ≤ (0.02 + qG X) * √(n : ℝ) * log n := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hlog : 0 ≤ log (n : ℝ) := log_nonneg hn1
  have hφ := half_totient hd
  have hφ0 : (0 : ℝ) < d.totient := by linarith
  have hpi := PaperInputs148.lemma1_of_grh h1 hG n (hX.trans hn)
  simp only [PaperInputs148.primeCount, Nat.floor_natCast] at hpi
  have hprog := h3 hG d n n n hd hdn le_rfl hc
  simp only [Nat.floor_natCast] at hprog
  have hmono := DecompC164a.qG_antitone X n (by linarith) hn
  have hprog' :
      |(((range (n + 1)).filter (fun p => p.Prime ∧ p % d = n % d)).card : ℝ) -
        liPV n / d.totient| ≤ qG X * √(n : ℝ) * log n := by
    exact hprog.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hmono (sqrt_nonneg _)) hlog)
  have hcorr :
      |liPV n - (((range (n + 1)).filter Nat.Prime).card : ℝ)| / d.totient ≤
        0.02 * √(n : ℝ) * log n := by
    rw [abs_sub_comm]
    calc
      _ ≤ (√(n : ℝ) * log n / (8 * π)) / d.totient :=
        div_le_div_of_nonneg_right hpi hφ0.le
      _ ≤ (√(n : ℝ) * log n / (8 * π)) / 2 := by gcongr
      _ = (1 / (16 * π)) * (√(n : ℝ) * log n) := by ring
      _ ≤ 0.02 * √(n : ℝ) * log n := by
        have hc : 1 / (16 * π) ≤ (0.02 : ℝ) := by
          rw [div_le_iff₀ (by positivity)]
          linarith [Real.pi_gt_d6]
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc
          (mul_nonneg (sqrt_nonneg (n : ℝ)) hlog)
  unfold ProgressionC169.progressionError
  rw [progressionPrimes_eq]
  calc
    _ = |((((range (n + 1)).filter (fun p => p.Prime ∧ p % d = n % d)).card : ℝ) -
          liPV n / d.totient) +
          (liPV n - (((range (n + 1)).filter Nat.Prime).card : ℝ)) / d.totient| := by
      congr 1; ring
    _ ≤ |(((range (n + 1)).filter (fun p => p.Prime ∧ p % d = n % d)).card : ℝ) -
          liPV n / d.totient| +
          |liPV n - (((range (n + 1)).filter Nat.Prime).card : ℝ)| / d.totient := by
      simpa only [abs_div, abs_of_pos hφ0] using abs_add_le
        ((((range (n + 1)).filter (fun p => p.Prime ∧ p % d = n % d)).card : ℝ) - liPV n / d.totient)
        ((liPV n - (((range (n + 1)).filter Nat.Prime).card : ℝ)) / d.totient)
    _ ≤ qG X * √(n : ℝ) * log n + 0.02 * √(n : ℝ) * log n := add_le_add hprog' hcorr
    _ = _ := by ring


/-- Sum the elementary residue comparison on arbitrary squarefree moduli, pp. 1230 and 1231.
CONDITIONAL ON the squarefree count and the stated progression envelope. -/
theorem squarefree_residue_sum_raw (hMu : PaperInputs148.Lemma5MuJ)
    (n : ℕ) (H E : ℝ) (s : Finset ℕ) (hn : 0 < n) (hH : 1 ≤ H) (hE : 0 ≤ E)
    (hs : ∀ d ∈ s, Squarefree d ∧ 1 ≤ d ∧ (d : ℝ) ≤ H)
    (herr : ∀ d ∈ s, |ProgressionC169.progressionError n d| ≤ E) :
    (∑ d ∈ s, |residue n d|) ≤
      Lemma5Coeffs138.mMu H * H * (E + n.primeFactors.card) := by
  calc
    _ ≤ ∑ d ∈ s, (E + n.primeFactors.card) := sum_le_sum fun d hd =>
      (ProgressionC169.residue_abs_le n d hn).trans (add_le_add (herr d hd) le_rfl)
    _ = (s.card : ℝ) * (E + n.primeFactors.card) := by simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (squarefree_count_le hMu s H hH hs)
      (by positivity)


/-- Condition 19 propagates from the threshold to every larger n, p. 1229.
This uses the already proved logarithmic monotonicity step. -/
theorem cond19_at (α A u X N : ℝ) (hα : 0 < α) (hA : 0 < A)
    (hc : Cond19 α A u X) (hX : 1 < X) (hXN : X ≤ N) :
    exp u ≤ N ^ α / log N ^ (A + 1) := by
  have hX0 : 0 < X := by linarith
  have hN0 : 0 < N := by linarith
  have hLX : 0 < log X := log_pos hX
  have hLN : 0 < log N := log_pos (hX.trans_le hXN)
  have hmono := Journal.mono_step hα (by linarith : 0 < A + 1) hc.1
    (log_le_log hX0 hXN)
  have heq (t : ℝ) (ht : 0 < t) (hlt : 0 < log t) :
      t ^ α / log t ^ (A + 1) = exp (α * log t - (A + 1) * log (log t)) := by
    rw [rpow_def_of_pos ht, rpow_def_of_pos hlt, ← exp_sub]
    congr 1; ring
  exact hc.2.1.trans (by
    rw [heq X hX0 hLX, heq N hN0 hLN]
    exact exp_le_exp.mpr hmono)


/-- Lemma 13 on any squarefree subset below the level, pp. 1230 and 1231.
CONDITIONAL ON Lemmas 1, 3, 4, 5 and GRH. No small-prime support is assumed. -/
theorem squarefree_residue_sum (h1 : PaperInputs148.Lemma1J)
    (h4 : PaperInputs148.Lemma4J) (hMu : PaperInputs148.Lemma5MuJ)
    (h3 : Lemma3J) (hG : GRH) (n : ℕ) (X A : ℝ) (s : Finset ℕ)
    (hX : 4e18 ≤ X) (hn : X ≤ (n : ℝ)) (hA : 0 < A) (hev : Even n)
    (hH : 1e8 ≤ √(n : ℝ) / log n ^ (A + 1))
    (hs : ∀ d ∈ s, Squarefree d ∧ 1 ≤ d ∧
      (d : ℝ) ≤ √(n : ℝ) / log n ^ (A + 1) ∧ Nat.Coprime d n) :
    (∑ d ∈ s, |residue n d|) ≤ cGJ X * n / log n ^ A := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hnNat : 0 < n := by exact_mod_cast hn0
  have hn3 : 3 ≤ n := by exact_mod_cast (show (3 : ℝ) ≤ n by linarith)
  have hL : 42.83 ≤ log (n : ℝ) := logX_bounds.1.trans
    (log_le_log (by norm_num) (hX.trans hn))
  have hLp : 0 < log (n : ℝ) := by linarith
  have hLL : 0 < log (log (n : ℝ)) := log_pos (by linarith)
  have hS : 0 < √(n : ℝ) := sqrt_pos.mpr hn0
  have hP : 0 < log (n : ℝ) ^ A := rpow_pos_of_pos hLp _
  have hP1 : 0 < log (n : ℝ) ^ (A + 1) := rpow_pos_of_pos hLp _
  have hpow : log (n : ℝ) ^ (A + 1) = log n ^ A * log n := by
    rw [rpow_add hLp, rpow_one]
  have hHsqrt : √(n : ℝ) / log n ^ (A + 1) ≤ √(n : ℝ) :=
    div_le_self hS.le (one_le_rpow (by linarith) (by linarith))
  have hq : 0 ≤ qG (n : ℝ) := EndpointC169.qG_nonneg n hn0 (by linarith)
  have hE : 0 ≤ (0.02 + qG (n : ℝ)) * √(n : ℝ) * log n := by positivity
  have herr (d : ℕ) (hd : d ∈ s) :
      |ProgressionC169.progressionError n d| ≤
        (0.02 + qG (n : ℝ)) * √(n : ℝ) * log n := by
    obtain ⟨_, hd1, hdH, hc⟩ := hs d hd
    by_cases hdOne : d = 1
    · subst d
      rw [progressionError_one, abs_zero]
      exact hE
    · have hd3 : 3 ≤ d := by
        by_contra h
        have hd2 : d = 2 := by omega
        subst d
        exact (Nat.prime_two.coprime_iff_not_dvd.mp hc) hev.two_dvd
      exact progression_error_le h1 h3 hG n d n (by linarith) le_rfl hd3
        (hdH.trans hHsqrt) hc.symm
  have hraw := squarefree_residue_sum_raw hMu n
    (√(n : ℝ) / log n ^ (A + 1))
    ((0.02 + qG (n : ℝ)) * √(n : ℝ) * log n) s hnNat
    (by linarith) hE (fun d hd => by obtain ⟨a,b,c,_⟩ := hs d hd; exact ⟨a,b,c⟩) herr
  have hcount := Lemma5Coeffs138.mMu_le0608 _ hH
  have hω := (h4 n hn3).le
  have hid : √(n : ℝ) / log n ^ (A + 1) * (√(n : ℝ) * log n) =
      (n : ℝ) / log n ^ A := by
    rw [hpow]
    field_simp
    nlinarith [sq_sqrt hn0.le]
  have htail :
      0.608 * (√(n : ℝ) / log n ^ (A + 1)) * n.primeFactors.card ≤
        (0.85 / (√(n : ℝ) * log (log n))) * ((n : ℝ) / log n ^ A) := by
    calc
      _ ≤ 0.608 * (√(n : ℝ) / log n ^ (A + 1)) *
          (1.3841 * log n / log (log n)) := by gcongr
      _ = (0.608 * 1.3841) / (√(n : ℝ) * log (log n)) * ((n : ℝ) / log n ^ A) := by
        rw [hpow]
        field_simp
        nlinarith [sq_sqrt hn0.le]
      _ ≤ _ := by
        gcongr
        norm_num
  have hraw' : (∑ d ∈ s, |residue n d|) ≤
      0.608 * (√(n : ℝ) / log n ^ (A + 1)) *
        ((0.02 + qG (n : ℝ)) * √(n : ℝ) * log n + n.primeFactors.card) := by
    apply hraw.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcount (by positivity)) (by positivity)
  have hnorm : (∑ d ∈ s, |residue n d|) ≤ cGJ (n : ℝ) * n / log n ^ A := by
    have heq : 0.608 * (√(n : ℝ) / log n ^ (A + 1)) *
        ((0.02 + qG (n : ℝ)) * √(n : ℝ) * log n) =
        pGJ n * ((n : ℝ) / log n ^ A) := by
      unfold pGJ
      calc
        _ = 0.608 * (0.02 + qG (n : ℝ)) *
            (√(n : ℝ) / log n ^ (A + 1) * (√(n : ℝ) * log n)) := by ring
        _ = _ := by rw [hid]
    calc
      _ ≤ _ := hraw'
      _ = 0.608 * (√(n : ℝ) / log n ^ (A + 1)) *
          ((0.02 + qG (n : ℝ)) * √(n : ℝ) * log n) +
          0.608 * (√(n : ℝ) / log n ^ (A + 1)) * n.primeFactors.card := by ring
      _ ≤ 0.608 * (√(n : ℝ) / log n ^ (A + 1)) *
          ((0.02 + qG (n : ℝ)) * √(n : ℝ) * log n) +
          (0.85 / (√(n : ℝ) * log (log n))) * ((n : ℝ) / log n ^ A) :=
        add_le_add le_rfl htail
      _ = _ := by rw [heq]; unfold cGJ; ring
  exact hnorm.trans (by
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_right
      (CoefficientsC169.cGJ_antitone X n hX hn) (div_nonneg hn0.le hP.le))


/-- The eligible small-prime product is bounded by exp theta, p. 1229. -/
theorem smallProduct_le_exp_theta (n : ℕ) (u : ℝ) :
    (smallProduct n u : ℝ) ≤ exp (Chebyshev.theta u) := by
  have hpos : 0 < (smallProduct n u : ℝ) := by
    rw [smallProduct, Nat.cast_prod]
    apply prod_pos
    intro p hp
    have hprime : p.Prime := (mem_filter.mp hp).2.1
    exact_mod_cast hprime.pos
  rw [← exp_log hpos]
  apply exp_le_exp.mpr
  rw [smallProduct, Nat.cast_prod, log_prod (fun p hp => by
    exact_mod_cast (mem_filter.mp hp).2.1.ne_zero), Chebyshev.theta_eq_sum_Icc]
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨_, hprime, _, hpu⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_floor hpu.le⟩, hprime⟩
  · intro p hp _
    exact log_nonneg (by exact_mod_cast (mem_filter.mp hp).2.one_le)


end
end LeanLab.BS2022GRH.DecompC169b
