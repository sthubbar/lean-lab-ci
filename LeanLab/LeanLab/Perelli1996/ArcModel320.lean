/-
Perelli 1996, page 481 equation 2, the prime model on the primary major arcs.
Split of Decomp320a.leaf_prime_model into a pointwise arc approximation, the
decomposition of the major arc integral into single arcs, and the summation over
the arcs with the Ramanujan sum weights.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.Definitions103
import LeanLab.Perelli1996.Series320
import LeanLab.Perelli1996.RamanujanInt400
import LeanLab.Perelli1996.Parseval103
import LeanLab.PNTPort.Vinogradov.MajorArcUncond

namespace LeanLab.Perelli1996.ArcModel320
open Finset Real MeasureTheory
open LeanLab.Perelli1996.Decomp88
noncomputable section

/-- An integer phase is trivial. -/
theorem e_intCast (k : ℤ) : Kernel.e (k : ℝ) = 1 := by
  unfold Kernel.e
  rw [show Complex.I * ((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) = k * (2 * Real.pi * Complex.I) by
    push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I k

/-- The additive kernel has modulus one. -/
theorem norm_e (x : ℝ) : ‖Kernel.e x‖ = 1 := by
  simp [Kernel.e, Complex.norm_exp]

/-- Integer frequencies are periodic with period one. -/
theorem e_int_mul_add_one (k : ℤ) (x : ℝ) : Kernel.e ((k : ℝ) * (x + 1)) = Kernel.e ((k : ℝ) * x) := by
  rw [mul_add, mul_one, Parseval103.e_add, e_intCast, mul_one]

/-- The coefficient integrand is continuous. -/
theorem coefficientIntegrand_continuous (M m : ℕ) : Continuous (coefficientIntegrand M m) := by
  unfold coefficientIntegrand primeSum Kernel.e
  fun_prop

/-- The coefficient integrand has period one. -/
theorem coefficientIntegrand_periodic (M m : ℕ) :
    Function.Periodic (coefficientIntegrand M m) 1 := by
  intro α
  unfold coefficientIntegrand primeSum
  have h1 : ∀ n : ℕ, Kernel.e ((n : ℝ) * (α + 1)) = Kernel.e ((n : ℝ) * α) := fun n => by
    simpa using e_int_mul_add_one (n : ℤ) α
  have h2 : Kernel.e (-(m : ℝ) * (α + 1)) = Kernel.e (-(m : ℝ) * α) := by
    simpa using e_int_mul_add_one (-(m : ℤ)) α
  simp only [h1, h2]

/-- The principal model weight mu q over phi q has modulus at most one. -/
theorem norm_model_le (q : ℕ) (hq : 0 < q) :
    ‖(ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)‖ ≤ 1 := by
  have hφ : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.2 hq
  rw [norm_div]
  have hμ : ‖(ArithmeticFunction.moebius q : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hφn : ‖(q.totient : ℂ)‖ = q.totient := by simp
  rw [hφn, div_le_one (by linarith)]
  linarith

/-- The prime sum of page 480 is the lab's Vinogradov sum S, since Lambda 0 is zero. -/
theorem primeSum_eq_S (M : ℕ) (α : ℝ) : primeSum M α = LeanLab.PNTPort.Vinogradov.S M α := by
  unfold primeSum LeanLab.PNTPort.Vinogradov.S
  symm
  apply Finset.sum_subset
  · intro x hx
    simp only [Finset.mem_Icc] at hx
    simp only [Finset.mem_range]
    omega
  · intro x hx hx'
    simp only [Finset.mem_Icc, Finset.mem_range] at hx hx'
    have : x = 0 := by omega
    subst this
    simp

/-- The kernel T on 0 to M is one plus the lab's Vinogradov kernel V. -/
theorem T_eq_one_add_V (M : ℕ) (η : ℝ) :
    Kernel.T 0 (M + 1) η = 1 + LeanLab.PNTPort.Vinogradov.V M η := by
  unfold Kernel.T LeanLab.PNTPort.Vinogradov.V
  rw [Finset.sum_range_succ', add_comm]
  congr 1
  · simp [Kernel.e]
  · have hI : Finset.Icc 1 M = Finset.Ico (0 + 1) (M + 1) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [hI, ← Finset.sum_Ico_add' (fun n : ℕ => LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * η)) 0 M 1,
      ← Finset.range_eq_Ico]
    apply Finset.sum_congr rfl
    intro n _
    simp only [zero_add]
    rfl

set_option maxHeartbeats 1600000 in
/-- Page 481 equation 2 via Vaughan 1981 Chapter 3, Lemma 3.1, from the
Siegel Walfisz theorem with partial summation: on the arc at a over q with q at most
L^B, the prime sum equals mu q over phi q times the kernel T up to an error saving any
fixed power of L. The radius L^B over N keeps the partial summation factor 1 plus N
times eta below a power of L. PROVED from LeanLab.PNTPort.Vinogradov.major_arc, which rests on
the lab's unconditional PNTPort.PsiChi.siegelWalfisz. -/
theorem leaf_arc_pointwise (c : ℝ) (hc : 0 < c) (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ Real.log N ^ B → ∀ a : ℕ, Nat.Coprime a q → ∀ η : ℝ,
      |η| ≤ Real.log N ^ B / N →
      ‖primeSum ⌊c * N⌋₊ ((a : ℝ) / q + η) -
        ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) *
          Kernel.T 0 (⌊c * N⌋₊ + 1) η‖ ≤ C * N * Real.log N ^ (-A) := by
  obtain ⟨c', hc', K, hK, hmaj⟩ := LeanLab.PNTPort.Vinogradov.major_arc (B + 1) (by positivity)
  set D := A + 2 * B with hD
  have hF1 := (isLittleO_log_rpow_rpow_atTop (D + 2) (by norm_num : (0 : ℝ) < 1 / 2)).bound
    (by norm_num : (0 : ℝ) < 1)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hF1
  have hsq : Filter.Tendsto (fun N : ℝ => Real.sqrt (Real.log N)) Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  have hF2 := (isLittleO_rpow_exp_pos_mul_atTop (2 * D) (by positivity : 0 < c' / 2)).bound
    (by norm_num : (0 : ℝ) < 1)
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp (hsq.eventually hF2)
  set N₀ := max (max 3 (max N₁ N₂))
    (max ((2 * Real.exp 4 + 2) / c) (Real.exp (2 * |Real.log (c / 2)| + 2 ^ (B + 1) + 1)))
    with hN₀def
  set C := (1 + 2 * π * c) * (7 * Real.sqrt c + K * c + (|Real.log c| + 1) / Real.log 2) + 2
    with hCdef
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C, N₀, by positivity, (le_max_left _ _).trans (le_max_left _ _), ?_⟩
  intro N hN q hq hqL a hcop η hη
  have hN3 : 3 ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hN1' : N₁ ≤ N :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hN
  have hN2' : N₂ ≤ N :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hN
  have hNc : (2 * Real.exp 4 + 2) / c ≤ N :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hNe : Real.exp (2 * |Real.log (c / 2)| + 2 ^ (B + 1) + 1) ≤ N :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  have hN0 : 0 < N := by linarith
  set L := Real.log N with hLdef
  have hLbig : 2 * |Real.log (c / 2)| + 2 ^ (B + 1) + 1 ≤ L := by
    have := Real.log_le_log (Real.exp_pos _) hNe
    rwa [Real.log_exp] at this
  have h2B : (0 : ℝ) < 2 ^ (B + 1) := by positivity
  have habs : 0 ≤ |Real.log (c / 2)| := abs_nonneg _
  have hL1 : 1 ≤ L := by linarith
  have hL : 0 < L := by linarith
  have hcN : 2 * Real.exp 4 + 2 ≤ c * N := by
    have := (div_le_iff₀ hc).mp hNc
    linarith
  set M := ⌊c * N⌋₊ with hMdef
  have hMhi : (M : ℝ) ≤ c * N := Nat.floor_le (by positivity)
  have hMlt : c * N < M + 1 := Nat.lt_floor_add_one _
  have he4 : 0 < Real.exp 4 := Real.exp_pos 4
  have hMlo : c * N / 2 ≤ M := by linarith
  have hM4 : Real.exp 4 ≤ M := by linarith
  have hMpos : (0 : ℝ) < M := by linarith
  set LM := Real.log M with hLMdef
  have hLMlo : L / 2 ≤ LM := by
    have h1 := Real.log_le_log (by positivity) hMlo
    rw [show c * N / 2 = (c / 2) * N by ring, Real.log_mul (by positivity) hN0.ne'] at h1
    have : -|Real.log (c / 2)| ≤ Real.log (c / 2) := neg_abs_le _
    linarith
  have hLMhi : LM ≤ (|Real.log c| + 1) * L := by
    have h1 := Real.log_le_log hMpos hMhi
    rw [Real.log_mul hc.ne' hN0.ne'] at h1
    have : Real.log c ≤ |Real.log c| := le_abs_self _
    nlinarith [abs_nonneg (Real.log c)]
  -- the modulus condition of the major arc lemma
  have hLB1 : 1 ≤ L ^ B := Real.one_le_rpow hL1 hB.le
  have hq' : (q : ℝ) ≤ LM ^ (B + 1) := by
    have h1 : L ^ B ≤ (L / 2) ^ (B + 1) := by
      rw [Real.div_rpow hL.le (by norm_num), Real.rpow_add_one hL.ne', Real.rpow_add_one
        (by norm_num : (2 : ℝ) ≠ 0)]
      rw [Real.rpow_add_one (by norm_num : (2 : ℝ) ≠ 0)] at h2B hLbig
      have hLB : 0 < L ^ B := by positivity
      have h2 : (0 : ℝ) < 2 ^ B := by positivity
      rw [le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left (show 2 ^ B * 2 ≤ L by linarith) hLB.le]
    have h2 : (L / 2) ^ (B + 1) ≤ LM ^ (B + 1) :=
      Real.rpow_le_rpow (by positivity) hLMlo (by positivity)
    linarith
  have hmaj' := hmaj M hM4 q hq hq' (a : ℤ) (Nat.isCoprime_iff_coprime.mpr hcop) η
  simp only [Int.cast_natCast] at hmaj'
  rw [primeSum_eq_S, T_eq_one_add_V]
  set d : ℂ := (ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ) with hd
  have hdn : ‖d‖ ≤ 1 := norm_model_le q hq
  have hsplit : LeanLab.PNTPort.Vinogradov.S M (a / q + η) - d * (1 +
      LeanLab.PNTPort.Vinogradov.V M η) =
      (LeanLab.PNTPort.Vinogradov.S M (a / q + η) - d * LeanLab.PNTPort.Vinogradov.V M η) - d := by
    ring
  rw [hsplit]
  refine (norm_sub_le _ _).trans ?_
  -- bounds on the pieces of the major arc error
  set E := Real.exp (-c' * (Real.sqrt L / 2)) with hEdef
  have hE0 : 0 < E := Real.exp_pos _
  have hY : 1 + 2 * π * |η| * M ≤ (1 + 2 * π * c) * L ^ B := by
    have h1 : |η| * M ≤ c * L ^ B := by
      calc |η| * M ≤ (L ^ B / N) * (c * N) := mul_le_mul hη hMhi (by positivity) (by positivity)
        _ = c * L ^ B := by field_simp
    nlinarith [Real.pi_pos]
  have hsqM : Real.sqrt M ≤ Real.sqrt c * Real.sqrt N := by
    rw [← Real.sqrt_mul hc.le]
    exact Real.sqrt_le_sqrt hMhi
  have hEM : Real.exp (-c' * Real.sqrt (LM / 2)) ≤ E := by
    apply Real.exp_le_exp.mpr
    have h1 : Real.sqrt L / 2 ≤ Real.sqrt (LM / 2) := by
      have h4 : Real.sqrt L / 2 = Real.sqrt (L / 4) := by
        rw [Real.sqrt_div' L (by norm_num : (0 : ℝ) ≤ 4),
          show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [h4]
      exact Real.sqrt_le_sqrt (by linarith)
    nlinarith
  have hlogq : Real.log q ≤ L ^ B := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < q by exact_mod_cast hq)
    linarith
  have hlogq0 : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have hLM0 : 0 ≤ LM := by linarith
  have hbr : 7 * Real.sqrt M + q * K * M * Real.exp (-c' * Real.sqrt (LM / 2)) +
      Real.log q / Real.log 2 * LM ≤
      7 * Real.sqrt c * Real.sqrt N + L ^ B * K * (c * N) * E +
        L ^ B * ((|Real.log c| + 1) * L) / Real.log 2 := by
    have t1 : 7 * Real.sqrt M ≤ 7 * Real.sqrt c * Real.sqrt N := by nlinarith
    have t2 : q * K * M * Real.exp (-c' * Real.sqrt (LM / 2)) ≤ L ^ B * K * (c * N) * E := by
      have := Real.exp_pos (-c' * Real.sqrt (LM / 2))
      gcongr
    have t3 : Real.log q / Real.log 2 * LM ≤ L ^ B * ((|Real.log c| + 1) * L) / Real.log 2 := by
      rw [div_mul_eq_mul_div]
      gcongr
    linarith
  -- the four comparisons with N L^(-A)
  have hLA : L ^ A * L ^ (-A) = 1 := by
    rw [Real.rpow_neg hL.le, mul_inv_cancel₀ (by positivity)]
  have hW0 : 0 < L ^ (-A) := by positivity
  have hF1N := hN₁ N hN1'
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity), one_mul] at hF1N
  have hsqN : Real.sqrt N = N ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow N
  have hsqN1 : Real.sqrt N ≤ N := by
    rw [Real.sqrt_le_left]
    · nlinarith
    · linarith
  have hsqsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  have hmono : ∀ x : ℝ, x ≤ D + 2 → L ^ x ≤ Real.sqrt N := fun x hx => by
    rw [hsqN]
    exact (Real.rpow_le_rpow_of_exponent_le hL1 hx).trans hF1N
  have w1 : Real.sqrt N * L ^ B ≤ N * L ^ (-A) := by
    have h1 : L ^ B * L ^ A ≤ Real.sqrt N := by
      rw [← Real.rpow_add hL]
      exact hmono _ (by rw [hD]; linarith)
    calc Real.sqrt N * L ^ B = Real.sqrt N * (L ^ B * L ^ A) * L ^ (-A) := by
          linear_combination (-(Real.sqrt N * L ^ B)) * hLA
      _ ≤ Real.sqrt N * Real.sqrt N * L ^ (-A) := by gcongr
      _ = N * L ^ (-A) := by rw [hsqsq]
  have w2 : L ^ B * L ^ B * E * N ≤ N * L ^ (-A) := by
    have hF2N := hN₂ N hN2'
    simp only [Real.norm_eq_abs] at hF2N
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity), one_mul] at hF2N
    have hpow : Real.sqrt L ^ (2 * D) = L ^ D := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hL.le]
      congr 1
      ring
    rw [hpow] at hF2N
    have h1 : L ^ B * L ^ B * L ^ A ≤ Real.exp (c' * (Real.sqrt L / 2)) := by
      rw [← Real.rpow_add hL, ← Real.rpow_add hL]
      calc L ^ (B + B + A) = L ^ D := by rw [hD]; congr 1; ring
        _ ≤ _ := by convert hF2N using 2; ring
    have hEE : Real.exp (c' * (Real.sqrt L / 2)) * E = 1 := by
      rw [hEdef, ← Real.exp_add]
      simp
    calc L ^ B * L ^ B * E * N = (L ^ B * L ^ B * L ^ A) * E * N * L ^ (-A) := by
          linear_combination (-(L ^ B * L ^ B * E * N)) * hLA
      _ ≤ Real.exp (c' * (Real.sqrt L / 2)) * E * N * L ^ (-A) := by gcongr
      _ = N * L ^ (-A) := by rw [hEE]; ring
  have w3 : L ^ B * L ^ B * L ≤ N * L ^ (-A) := by
    have h1 : L ^ B * L ^ B * L * L ^ A ≤ N := by
      have : L ^ B * L ^ B * L * L ^ A = L ^ (B + B + 1 + A) := by
        rw [Real.rpow_add hL, Real.rpow_add hL, Real.rpow_add hL, Real.rpow_one]
      rw [this]
      exact (hmono _ (by rw [hD]; linarith)).trans hsqN1
    calc L ^ B * L ^ B * L = (L ^ B * L ^ B * L * L ^ A) * L ^ (-A) := by
          linear_combination (-(L ^ B * L ^ B * L)) * hLA
      _ ≤ N * L ^ (-A) := by gcongr
  have w4 : 1 ≤ N * L ^ (-A) := by
    have h1 : L ^ A ≤ N := (hmono _ (by rw [hD]; linarith)).trans hsqN1
    calc (1 : ℝ) = L ^ A * L ^ (-A) := hLA.symm
      _ ≤ N * L ^ (-A) := by gcongr
  have hY0 : 0 ≤ 1 + 2 * π * |η| * M := by positivity
  have hbr0 : 0 ≤ 7 * Real.sqrt c * Real.sqrt N + L ^ B * K * (c * N) * E +
        L ^ B * ((|Real.log c| + 1) * L) / Real.log 2 := by positivity
  have hX := mul_le_mul hbr hY hY0 hbr0
  have hexpand : (7 * Real.sqrt c * Real.sqrt N + L ^ B * K * (c * N) * E +
        L ^ B * ((|Real.log c| + 1) * L) / Real.log 2) * ((1 + 2 * π * c) * L ^ B) =
      (1 + 2 * π * c) * (7 * Real.sqrt c * (Real.sqrt N * L ^ B) +
        K * c * (L ^ B * L ^ B * E * N) +
        (|Real.log c| + 1) / Real.log 2 * (L ^ B * L ^ B * L)) := by
    field_simp
  rw [hexpand] at hX
  have hk1 : 0 ≤ 1 + 2 * π * c := by positivity
  have hk2 : 0 ≤ 7 * Real.sqrt c := by positivity
  have hk3 : 0 ≤ K * c := by positivity
  have hk4 : 0 ≤ (|Real.log c| + 1) / Real.log 2 := by positivity
  have hsum : 7 * Real.sqrt c * (Real.sqrt N * L ^ B) + K * c * (L ^ B * L ^ B * E * N) +
      (|Real.log c| + 1) / Real.log 2 * (L ^ B * L ^ B * L) ≤
      (7 * Real.sqrt c + K * c + (|Real.log c| + 1) / Real.log 2) * (N * L ^ (-A)) := by
    have := mul_le_mul_of_nonneg_left w1 hk2
    have := mul_le_mul_of_nonneg_left w2 hk3
    have := mul_le_mul_of_nonneg_left w3 hk4
    nlinarith
  have hX2 := hX.trans (mul_le_mul_of_nonneg_left hsum hk1)
  calc _ ≤ (1 + 2 * π * c) * ((7 * Real.sqrt c + K * c + (|Real.log c| + 1) / Real.log 2) *
          (N * L ^ (-A))) + 1 := add_le_add (hmaj'.trans hX2) hdn
    _ ≤ C * N * L ^ (-A) := by
      rw [hCdef]
      nlinarith

/-- Coprimality of an integer numerator with a natural modulus. -/
theorem coprime_iff_isCoprime (a : ℤ) (q : ℕ) : Nat.Coprime a.natAbs q ↔ IsCoprime a (q : ℤ) := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  rfl

/-- Page 480: the primary major arcs are invariant under translation by one. -/
theorem mem_majorArcs_add_one (N B α : ℝ) : α + 1 ∈ majorArcs N B ↔ α ∈ majorArcs N B := by
  constructor
  · rintro ⟨q, hq, hqB, a, hcop, hα⟩
    refine ⟨q, hq, hqB, a - q, ?_, ?_⟩
    · rw [coprime_iff_isCoprime] at hcop ⊢
      have := hcop.add_mul_left_left (-1)
      rwa [mul_neg_one, ← sub_eq_add_neg] at this
    · have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
      have : α - ((a - q : ℤ) : ℝ) / q = α + 1 - (a : ℝ) / q := by
        push_cast; field_simp; ring
      rwa [this]
  · rintro ⟨q, hq, hqB, a, hcop, hα⟩
    refine ⟨q, hq, hqB, a + q, ?_, ?_⟩
    · rw [coprime_iff_isCoprime] at hcop ⊢
      have := hcop.add_mul_left_left 1
      rwa [mul_one] at this
    · have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
      have : α + 1 - ((a + q : ℤ) : ℝ) / q = α - (a : ℝ) / q := by
        push_cast; field_simp; ring
      rwa [this]

/-- Page 480: two primary arcs with moduli at most P and radius r, 2 r P^2 below one, meet
only when they are the same arc. -/
theorem arcs_eq_of_mem (P r : ℝ) (hsmall : 2 * r * (P * P) < 1) (q q' a a' : ℕ)
    (hq : 1 ≤ q) (hq' : 1 ≤ q') (hqP : (q : ℝ) ≤ P) (hqP' : (q' : ℝ) ≤ P)
    (hc : Nat.Coprime a q) (hc' : Nat.Coprime a' q') (x : ℝ)
    (hx : x ∈ Set.Icc ((a : ℝ) / q - r) ((a : ℝ) / q + r))
    (hx' : x ∈ Set.Icc ((a' : ℝ) / q' - r) ((a' : ℝ) / q' + r)) : q = q' ∧ a = a' := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq0' : (0 : ℝ) < q' := by exact_mod_cast hq'
  have hdiff : |(a : ℝ) / q - (a' : ℝ) / q'| ≤ 2 * r := by
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hx'.1, hx'.2]
  have hk : ((a * q' : ℕ) : ℝ) - ((a' * q : ℕ) : ℝ) = ((a : ℝ) / q - (a' : ℝ) / q') * (q * q') := by
    push_cast; field_simp
  have hqq : (q : ℝ) * q' ≤ P * P := mul_le_mul hqP hqP' hq0'.le (hq0.le.trans hqP)
  have hbound : |((a * q' : ℕ) : ℝ) - ((a' * q : ℕ) : ℝ)| < 1 := by
    rw [hk, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < q * q')]
    have hr0 : 0 ≤ r := by linarith [abs_nonneg ((a : ℝ) / q - (a' : ℝ) / q')]
    calc |(a : ℝ) / q - (a' : ℝ) / q'| * (q * q') ≤ 2 * r * (q * q') := by gcongr
      _ ≤ 2 * r * (P * P) := by gcongr
      _ < 1 := hsmall
  have heq : a * q' = a' * q := by
    rw [abs_lt] at hbound
    have h1 : ((a * q' : ℕ) : ℤ) - ((a' * q : ℕ) : ℤ) < 1 := by
      have := hbound.2; exact_mod_cast this
    have h2 : -1 < ((a * q' : ℕ) : ℤ) - ((a' * q : ℕ) : ℤ) := by
      have := hbound.1; exact_mod_cast this
    omega
  have hd1 : q ∣ q' := by
    have : q ∣ q' * a := ⟨a', by rw [mul_comm q' a, heq, mul_comm]⟩
    exact hc.symm.dvd_of_dvd_mul_right this
  have hd2 : q' ∣ q := by
    have : q' ∣ q * a' := ⟨a, by rw [mul_comm q a', ← heq, mul_comm]⟩
    exact hc'.symm.dvd_of_dvd_mul_right this
  have hqq' : q = q' := Nat.dvd_antisymm hd1 hd2
  refine ⟨hqq', ?_⟩
  subst hqq'
  exact Nat.eq_of_mul_eq_mul_right hq heq

/-- PROVED. Page 480, definition of the primary major arcs: for N large the arcs at a over q
with q at most L^B and radius L^B over N are disjoint, the arcs at 0 and 1 join by
periodicity, and the integral over the major arcs in the unit interval is the sum of the
integrals over the single arcs, indexed by q at most L^B and the reduced residues a. -/
theorem leaf_arc_integral_split (B : ℝ) (hB : 0 < B) :
    ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ f : ℝ → ℂ, Continuous f →
      Function.Periodic f 1 →
      ∫ α in Set.Icc 0 1 ∩ majorArcs N B, f α =
        ∑ q ∈ Icc 1 ⌊Real.log N ^ B⌋₊, ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          ∫ η in (-(Real.log N ^ B / N))..(Real.log N ^ B / N), f ((a : ℝ) / q + η) := by
  have hF := (isLittleO_log_rpow_rpow_atTop (3 * B) (by norm_num : (0 : ℝ) < 1)).bound
    (by norm_num : (0 : ℝ) < 1 / 4)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hF
  refine ⟨max 3 N₁, le_max_left _ _, ?_⟩
  intro N hN f hf hper
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hN0 : 0 < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  set P := Real.log N ^ B with hP
  set r := P / N with hr
  have hP0 : 0 < P := by positivity
  have hr0 : 0 < r := by positivity
  have hsmall : 2 * r * (P * P) < 1 := by
    have h1 := hN₁ N ((le_max_right _ _).trans hN)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity), Real.rpow_one] at h1
    have h3 : Real.log N ^ (3 * B) = P * P * P := by
      rw [hP, ← Real.rpow_add hL, ← Real.rpow_add hL]; congr 1; ring
    rw [h3] at h1
    have : 2 * r * (P * P) = 2 * (P * P * P) / N := by rw [hr]; field_simp
    rw [this, div_lt_one hN0]
    linarith
  have hqr : ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ P → 2 * r * q < 1 := by
    intro q hq hqP
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have : (q : ℝ) ≤ P * P := by nlinarith
    calc 2 * r * q ≤ 2 * r * (P * P) := by gcongr
      _ < 1 := hsmall
  have hinv : ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ P → 2 * r < 1 / q := by
    intro q hq hqP
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
    rw [lt_div_iff₀ hq0]
    exact hqr q hq hqP
  have hMA : MeasurableSet (majorArcs N B) := by
    unfold majorArcs; measurability
  have hgper : Function.Periodic ((majorArcs N B).indicator f) 1 := by
    intro α
    simp only [Set.indicator, hper α]
    by_cases h : α ∈ majorArcs N B
    · rw [if_pos ((mem_majorArcs_add_one N B α).mpr h), if_pos h]
    · rw [if_neg (fun h' => h ((mem_majorArcs_add_one N B α).mp h')), if_neg h]
  set Q := ⌊P⌋₊ with hQ
  let idx := (Icc 1 Q).sigma (fun q => (range q).filter (fun a => Nat.Coprime a q))
  let J : (Σ _ : ℕ, ℕ) → Set ℝ := fun i => Set.Icc ((i.2 : ℝ) / i.1 - r) ((i.2 : ℝ) / i.1 + r)
  have hmemidx : ∀ i ∈ idx, 1 ≤ i.1 ∧ (i.1 : ℝ) ≤ P ∧ i.2 < i.1 ∧ Nat.Coprime i.2 i.1 := by
    intro i hi
    simp only [idx, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter, Finset.mem_range] at hi
    exact ⟨hi.1.1, (Nat.cast_le.mpr hi.1.2).trans (Nat.floor_le hP0.le), hi.2.1, hi.2.2⟩
  have step1 : ∫ α in Set.Icc 0 1 ∩ majorArcs N B, f α =
      ∫ α in (0 : ℝ)..1, (majorArcs N B).indicator f α := by
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
      setIntegral_indicator hMA]
  have step2 : ∫ α in (0 : ℝ)..1, (majorArcs N B).indicator f α =
      ∫ α in Set.Ioc (-r) (-r + 1) ∩ majorArcs N B, f α := by
    have := hgper.intervalIntegral_add_eq 0 (-r)
    rw [zero_add] at this
    rw [this, intervalIntegral.integral_of_le (by linarith), setIntegral_indicator hMA]
  have hae : (Set.Ioc (-r) (-r + 1) ∩ majorArcs N B : Set ℝ) =ᵐ[volume] ⋃ i ∈ idx, J i := by
    rw [MeasureTheory.ae_eq_set]
    constructor
    · apply measure_mono_null _ (measure_singleton (-r + 1))
      rintro α ⟨⟨⟨hlo, hhi⟩, q, hq, hqP, a, hcop, hα⟩, hU⟩
      rw [Set.mem_singleton_iff]
      by_contra hne
      apply hU
      rw [abs_le] at hα
      have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
      have h2r := hinv q hq hqP
      rcases lt_or_ge a 0 with ha | ha
      · exfalso
        have ha1 : (a : ℝ) ≤ -1 := by exact_mod_cast (show a ≤ -1 by omega)
        have : (a : ℝ) / q ≤ -1 / q := div_le_div_of_nonneg_right ha1 hq0.le
        have h1q : -1 / (q : ℝ) = -(1 / q) := by ring
        linarith
      rcases lt_or_ge a q with haq | haq
      · lift a to ℕ using ha
        simp only [Set.mem_iUnion]
        refine ⟨⟨q, a⟩, ?_, ?_⟩
        · simp only [idx, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter, Finset.mem_range]
          refine ⟨⟨hq, Nat.le_floor hqP⟩, by exact_mod_cast haq, ?_⟩
          simpa using hcop
        · simp only [J, Set.mem_Icc]
          push_cast at hα
          constructor <;> linarith
      · exfalso
        have ha1 : (q : ℝ) ≤ a := by exact_mod_cast haq
        have : (1 : ℝ) ≤ (a : ℝ) / q := by rw [le_div_iff₀ hq0]; linarith
        apply hne
        linarith
    · apply measure_mono_null _ (measure_singleton (-r))
      intro α hα
      simp only [Set.mem_diff, Set.mem_iUnion] at hα
      obtain ⟨⟨i, hi, hαi⟩, hn⟩ := hα
      obtain ⟨hq1, hqP, haq, hcop⟩ := hmemidx i hi
      rw [Set.mem_singleton_iff]
      by_contra hne
      apply hn
      have hq0 : (0 : ℝ) < i.1 := by exact_mod_cast hq1
      have h2r := hinv i.1 hq1 hqP
      simp only [J, Set.mem_Icc] at hαi
      have ha0 : (0 : ℝ) ≤ (i.2 : ℝ) / i.1 := by positivity
      have haq' : (i.2 : ℝ) + 1 ≤ i.1 := by exact_mod_cast haq
      have hfrac0 : (i.2 : ℝ) / i.1 ≤ ((i.1 : ℝ) - 1) / i.1 :=
        div_le_div_of_nonneg_right (by linarith) hq0.le
      have hfrace : ((i.1 : ℝ) - 1) / i.1 = 1 - 1 / i.1 := by field_simp
      refine ⟨⟨lt_of_le_of_ne (by linarith) (Ne.symm hne), by linarith⟩, i.1, hq1, hqP,
        (i.2 : ℤ), by simpa using hcop, ?_⟩
      rw [abs_le]; push_cast; constructor <;> linarith
  have hdisj : Set.Pairwise (↑idx) (Function.onFun Disjoint J) := by
    intro i hi j hj hij
    show Disjoint (J i) (J j)
    rw [Set.disjoint_left]
    intro x hxi hxj
    obtain ⟨hq1, hqP, -, hcop⟩ := hmemidx i hi
    obtain ⟨hq1', hqP', -, hcop'⟩ := hmemidx j hj
    obtain ⟨h1, h2⟩ := arcs_eq_of_mem P r hsmall i.1 j.1 i.2 j.2 hq1 hq1' hqP hqP' hcop hcop'
      x hxi hxj
    exact hij (Sigma.ext h1 (heq_of_eq h2))
  rw [step1, step2, setIntegral_congr_set hae,
    integral_biUnion_finset idx (fun i _ => measurableSet_Icc) hdisj
      (fun i _ => hf.integrableOn_Icc), Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro a _
  simp only [J]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_comp_add_left f ((a : ℝ) / q), sub_eq_add_neg]

/-- Page 481 equation 2: the Ramanujan coefficient as a sum over reduced residues of the
squared principal model weight times the phase at minus m a over q. -/
theorem coefficient_eq_sum (m q : ℕ) (hq : 0 < q) :
    Series320.coefficient m q =
      ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) ^ 2 *
          Kernel.e (-(m : ℝ) * ((a : ℝ) / q)) := by
  unfold Series320.coefficient
  have h := RamanujanInt400.ramanujanSumInt_eq_natAbs q (-(m : ℤ)) hq
  simp only [Int.natAbs_neg, Int.natAbs_natCast] at h
  rw [← h, RamanujanInt400.ramanujanSumInt, Finset.mul_sum, div_pow]
  apply Finset.sum_congr rfl
  intro a _
  congr 2
  push_cast
  ring

/-- Page 481 equation 2, PROVED from leaf_arc_pointwise and leaf_arc_integral_split, both proved:
the major arc integral of the coefficient integrand is the finite singular partial sum
times the central kernel integral, up to N L^(-A/2). The error on each arc is the
pointwise error times twice the kernel bound times the arc length, and there are at
most L^(2B) arcs. -/
theorem arc_model (c : ℝ) (hc : 0 < c) (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ m : ℕ,
      ‖(∫ α in Set.Icc 0 1 ∩ majorArcs N B, coefficientIntegrand ⌊c * N⌋₊ m α) -
        (∑ q ∈ Icc 1 ⌊Real.log N ^ B⌋₊, Series320.coefficient m q) *
          (∫ α in (-(Real.log N ^ B / N))..(Real.log N ^ B / N),
            Kernel.T 0 (⌊c * N⌋₊ + 1) α ^ 2 * Kernel.e (-(m : ℝ) * α))‖ ≤
        C * N * Real.log N ^ (-A / 2) := by
  obtain ⟨N₁, hN₁, hsplit⟩ := leaf_arc_integral_split B hB
  obtain ⟨C₁, N₂, hC₁, hN₂, hpt⟩ := leaf_arc_pointwise c hc (3 * B + A / 2) B
    (by positivity) hB
  refine ⟨2 * C₁ * (C₁ + 2 * c + 2), max (max N₁ N₂) (Real.exp 1), by positivity,
    hN₁.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro N hN m
  have hN₁' : N₁ ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hN₂' : N₂ ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hNe : Real.exp 1 ≤ N := (le_max_right _ _).trans hN
  have hN3 : 3 ≤ N := hN₁.trans hN₁'
  have hN0 : 0 < N := by linarith
  have hL1 : 1 ≤ Real.log N := by simpa using Real.log_le_log (Real.exp_pos 1) hNe
  have hL : 0 < Real.log N := by linarith
  set M := ⌊c * N⌋₊ with hM
  set L := Real.log N with hLdef
  set r := L ^ B / N with hr
  set Q := ⌊L ^ B⌋₊ with hQ
  have hr0 : 0 ≤ r := by positivity
  set ε := C₁ * N * L ^ (-(3 * B + A / 2)) with hε
  have hε0 : 0 ≤ ε := by positivity
  have hεN : ε ≤ C₁ * N := by
    have : L ^ (-(3 * B + A / 2)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by
      have : 0 < 3 * B + A / 2 := by positivity
      linarith)
    calc ε = C₁ * N * L ^ (-(3 * B + A / 2)) := rfl
      _ ≤ C₁ * N * 1 := by gcongr
      _ = C₁ * N := by ring
  have hMN : (M : ℝ) ≤ c * N := Nat.floor_le (by positivity)
  set d : ℕ → ℂ := fun q => (ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ) with hd
  set g : ℝ → ℂ := fun η => Kernel.T 0 (M + 1) η ^ 2 * Kernel.e (-(m : ℝ) * η) with hg
  have hgc : Continuous g := by
    simp only [hg, Kernel.T, Kernel.e]
    fun_prop
  have hfc := coefficientIntegrand_continuous M m
  rw [hsplit N hN₁' _ hfc (coefficientIntegrand_periodic M m)]
  -- rewrite the main term as a sum over the arcs
  have hmain : (∑ q ∈ Icc 1 Q, Series320.coefficient m q) * (∫ η in (-r)..r, g η) =
      ∑ q ∈ Icc 1 Q, ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ∫ η in (-r)..r, d q ^ 2 * Kernel.e (-(m : ℝ) * ((a : ℝ) / q)) * g η := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q hq
    rw [coefficient_eq_sum m q (Finset.mem_Icc.mp hq).1, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [intervalIntegral.integral_const_mul]
  rw [hmain, ← Finset.sum_sub_distrib]
  -- the bound on one arc
  have harc : ∀ q ∈ Icc 1 Q, ∀ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      ‖(∫ η in (-r)..r, coefficientIntegrand M m ((a : ℝ) / q + η)) -
        ∫ η in (-r)..r, d q ^ 2 * Kernel.e (-(m : ℝ) * ((a : ℝ) / q)) * g η‖ ≤
        ε * (ε + 2 * (M + 1)) * (2 * r) := by
    intro q hq a ha
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hqQ : (q : ℝ) ≤ L ^ B :=
      (Nat.cast_le.mpr (Finset.mem_Icc.mp hq).2).trans (Nat.floor_le (by positivity))
    have hcop : Nat.Coprime a q := (Finset.mem_filter.mp ha).2
    have hi1 : IntervalIntegrable (fun η => coefficientIntegrand M m ((a : ℝ) / q + η))
        volume (-r) r := by
      apply Continuous.intervalIntegrable
      exact hfc.comp (continuous_const.add continuous_id)
    have hi2 : IntervalIntegrable
        (fun η => d q ^ 2 * Kernel.e (-(m : ℝ) * ((a : ℝ) / q)) * g η) volume (-r) r := by
      apply Continuous.intervalIntegrable
      exact continuous_const.mul hgc
    rw [← intervalIntegral.integral_sub hi1 hi2]
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -r) (b := r) (C := ε * (ε + 2 * (M + 1)))
      (f := fun η => coefficientIntegrand M m ((a : ℝ) / q + η) -
        d q ^ 2 * Kernel.e (-(m : ℝ) * ((a : ℝ) / q)) * g η) ?_
    · have hlen : |r - -r| = 2 * r := by rw [abs_of_nonneg (by linarith)]; ring
      simpa only [hlen] using hbound
    intro η hη
    have hηr : |η| ≤ r := by
      rw [Set.uIoc_of_le (by linarith)] at hη
      exact abs_le.mpr ⟨hη.1.le, hη.2⟩
    have hE := hpt N hN₂' q hq1 hqQ a hcop η hηr
    set S := primeSum M ((a : ℝ) / q + η) with hS
    set T := Kernel.T 0 (M + 1) η with hT
    have hdT : ‖d q * T‖ ≤ M + 1 := by
      rw [norm_mul]
      have h1 := norm_model_le q hq1
      have h2 : ‖T‖ ≤ ((M + 1 : ℕ) : ℝ) := Kernel.norm_T_le 0 (M + 1) η
      push_cast at h2
      calc ‖d q‖ * ‖T‖ ≤ 1 * (M + 1) := by gcongr
        _ = M + 1 := one_mul _
    have hphase : Kernel.e (-(m : ℝ) * ((a : ℝ) / q + η)) =
        Kernel.e (-(m : ℝ) * ((a : ℝ) / q)) * Kernel.e (-(m : ℝ) * η) := by
      rw [mul_add, Parseval103.e_add]
    have hexp : coefficientIntegrand M m ((a : ℝ) / q + η) -
        d q ^ 2 * Kernel.e (-(m : ℝ) * ((a : ℝ) / q)) * g η =
        Kernel.e (-(m : ℝ) * ((a : ℝ) / q)) * Kernel.e (-(m : ℝ) * η) *
          ((S - d q * T) * ((S - d q * T) + 2 * (d q * T))) := by
      simp only [coefficientIntegrand, hg, hphase]
      rw [← hS, ← hT]
      ring
    rw [hexp, norm_mul, norm_mul, norm_e, norm_e, one_mul, one_mul, norm_mul]
    have hsum : ‖(S - d q * T) + 2 * (d q * T)‖ ≤ ε + 2 * (M + 1) := by
      calc ‖(S - d q * T) + 2 * (d q * T)‖ ≤ ‖S - d q * T‖ + ‖2 * (d q * T)‖ := norm_add_le _ _
        _ = ‖S - d q * T‖ + 2 * ‖d q * T‖ := by rw [norm_mul]; norm_num
        _ ≤ ε + 2 * (M + 1) := by gcongr
    exact mul_le_mul hE hsum (norm_nonneg _) hε0
  -- count the arcs
  have hcount : ∑ q ∈ Icc 1 Q, ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      ε * (ε + 2 * (M + 1)) * (2 * r) ≤ (Q : ℝ) * Q * (ε * (ε + 2 * (M + 1)) * (2 * r)) := by
    have hX : 0 ≤ ε * (ε + 2 * (M + 1)) * (2 * r) := by positivity
    calc ∑ q ∈ Icc 1 Q, ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          ε * (ε + 2 * (M + 1)) * (2 * r)
        ≤ ∑ q ∈ Icc 1 Q, (Q : ℝ) * (ε * (ε + 2 * (M + 1)) * (2 * r)) := by
          apply Finset.sum_le_sum
          intro q hq
          rw [Finset.sum_const, nsmul_eq_mul]
          gcongr
          have h1 : ((range q).filter (fun a => Nat.Coprime a q)).card ≤ q :=
            (Finset.card_filter_le _ _).trans (by simp)
          exact_mod_cast h1.trans (Finset.mem_Icc.mp hq).2
      _ = (Q : ℝ) * Q * (ε * (ε + 2 * (M + 1)) * (2 * r)) := by
          rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
          simp only [add_tsub_cancel_right]
          ring
  have hQB : (Q : ℝ) ≤ L ^ B := Nat.floor_le (by positivity)
  have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
  have hfinal : (Q : ℝ) * Q * (ε * (ε + 2 * (M + 1)) * (2 * r)) ≤
      2 * C₁ * (C₁ + 2 * c + 2) * N * L ^ (-A / 2) := by
    have hinner : ε + 2 * ((M : ℝ) + 1) ≤ (C₁ + 2 * c + 2) * N := by
      nlinarith
    have hpow : L ^ B * L ^ B * L ^ B * L ^ (-(3 * B + A / 2)) = L ^ (-A / 2) := by
      rw [← Real.rpow_add hL, ← Real.rpow_add hL, ← Real.rpow_add hL]
      congr 1
      ring
    have hQQ : (Q : ℝ) * Q ≤ L ^ B * L ^ B := mul_le_mul hQB hQB hQ0 (by positivity)
    calc (Q : ℝ) * Q * (ε * (ε + 2 * (M + 1)) * (2 * r))
        ≤ L ^ B * L ^ B * (ε * ((C₁ + 2 * c + 2) * N) * (2 * r)) := by
          apply mul_le_mul hQQ _ (by positivity) (by positivity)
          gcongr
      _ = 2 * C₁ * (C₁ + 2 * c + 2) * N * (L ^ B * L ^ B * L ^ B * L ^ (-(3 * B + A / 2))) := by
          rw [hε, hr]
          field_simp
      _ = 2 * C₁ * (C₁ + 2 * c + 2) * N * L ^ (-A / 2) := by rw [hpow]
  calc _ ≤ ∑ q ∈ Icc 1 Q, ‖(∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          ∫ η in (-r)..r, coefficientIntegrand M m ((a : ℝ) / q + η)) -
        ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          ∫ η in (-r)..r, d q ^ 2 * Kernel.e (-(m : ℝ) * ((a : ℝ) / q)) * g η‖ :=
        norm_sum_le _ _
    _ ≤ ∑ q ∈ Icc 1 Q, ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ε * (ε + 2 * (M + 1)) * (2 * r) := by
        apply Finset.sum_le_sum
        intro q hq
        rw [← Finset.sum_sub_distrib]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun a ha => harc q hq a ha))
    _ ≤ _ := hcount
    _ ≤ _ := hfinal

end
end LeanLab.Perelli1996.ArcModel320
