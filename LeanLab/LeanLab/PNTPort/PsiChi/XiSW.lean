import LeanLab.PNTPort.PsiChi.SiegelWalfisz
import LeanLab.PNTPort.PsiChi.XiLink

/-!
# Xi 2012's hypothesis (3) for all primes, from Siegel-Walfisz

Lab proof, unit U-5213, CLOUD 20261019T0514Z-cloud17. AI wrote this file. Known mathematics, no
cited input; uses the re-encoded `Xi2012.theta`, congruence on `ℕ`.

* `xi_theta_eq`, `psi_sub_xi_theta`: for `A = primes ≤ x` and `0 ≤ y ≤ x`, `ϑ(y; q, a)` is the
  prime part of `ψ(y; q, a)`, and `0 ≤ ψ(y; q, a) - ϑ(y; q, a) ≤ ψ(y) - θ(y)`;
* `xi_siegelWalfisz : Xi2012.SiegelWalfisz primesUpTo (fun _ => 1)`, from `siegelWalfisz` with
  exponent `2c`, trivially for `y < max(√x, e²)`;
* `xi_classical_of_theorem2`: Xi's remark, Theorem 2 at any `c₀ > 0` gives the classical log power
  saving, CONDITIONAL ON Xi's Theorem 2 only.
-/

open Real Finset

open ArithmeticFunction (vonMangoldt)

local notation "Λ" => vonMangoldt

namespace LeanLab.PNTPort.PsiChi

lemma xi_theta_eq (x : ℕ) {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ x) (q a : ℕ) :
    Xi2012.theta (Xi2012.primesUpTo x) y q a =
      ∑ n ∈ (Icc 1 ⌊y⌋₊).filter (fun n => n % q = a % q ∧ n.Prime), Λ n := by
  classical
  unfold Xi2012.theta Xi2012.primesUpTo
  have hfl : ⌊y⌋₊ ≤ x := Nat.floor_le_of_le hy
  apply Finset.sum_congr
  · ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨h1, _⟩, hp⟩, hny, hm⟩
      exact ⟨⟨h1, Nat.le_floor hny⟩, hm, hp⟩
    · rintro ⟨⟨h1, h2⟩, hm, hp⟩
      exact ⟨⟨⟨h1, h2.trans hfl⟩, hp⟩, (Nat.le_floor_iff hy0).mp h2, hm⟩
  · intro n hn
    have hp := ((Finset.mem_filter.mp hn).2).2
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp]

lemma Icc_eq_Ioc (y : ℝ) : Finset.Ioc 0 ⌊y⌋₊ = Icc 1 ⌊y⌋₊ := by ext n; simp; omega

lemma xi_theta_le_psi (x : ℕ) {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ x) (q a : ℕ) :
    0 ≤ Xi2012.theta (Xi2012.primesUpTo x) y q a ∧
    Xi2012.theta (Xi2012.primesUpTo x) y q a ≤ Chebyshev.psi y := by
  rw [xi_theta_eq x hy0 hy, Chebyshev.psi, Icc_eq_Ioc]
  refine ⟨Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg, ?_⟩
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)

lemma psi_sub_xi_theta (x : ℕ) {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ x) (q a : ℕ) :
    0 ≤ HeathBrown1985.psi y q a - Xi2012.theta (Xi2012.primesUpTo x) y q a ∧
    HeathBrown1985.psi y q a - Xi2012.theta (Xi2012.primesUpTo x) y q a ≤
      Chebyshev.psi y - Chebyshev.theta y := by
  classical
  rw [xi_theta_eq x hy0 hy]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    ((Icc 1 ⌊y⌋₊).filter (fun n => n % q = a % q)) (fun n => n.Prime) (fun n => Λ n)
  rw [Finset.filter_filter, Finset.filter_filter] at hsplit
  unfold HeathBrown1985.psi
  rw [← hsplit, add_sub_cancel_left]
  have hψ : Chebyshev.psi y = ∑ n ∈ (Icc 1 ⌊y⌋₊).filter (fun n => n.Prime), Λ n +
      ∑ n ∈ (Icc 1 ⌊y⌋₊).filter (fun n => ¬ n.Prime), Λ n := by
    rw [Finset.sum_filter_add_sum_filter_not, Chebyshev.psi, Icc_eq_Ioc]
  have hθ : Chebyshev.theta y = ∑ n ∈ (Icc 1 ⌊y⌋₊).filter (fun n => n.Prime), Λ n := by
    rw [Chebyshev.theta, Icc_eq_Ioc]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hn).2]
  rw [hψ, hθ, add_sub_cancel_left]
  constructor
  · exact Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [Finset.mem_filter] at hn ⊢
      exact ⟨hn.1, hn.2.2⟩
    · intro _ _ _; exact ArithmeticFunction.vonMangoldt_nonneg

lemma rpow_two_mul_eq {u c : ℝ} (hu : 0 ≤ u) : (u ^ 2) ^ c = u ^ (2 * c) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hu]; norm_num

set_option maxHeartbeats 1600000 in
theorem xi_siegelWalfisz : Xi2012.SiegelWalfisz Xi2012.primesUpTo (fun _ => 1) := by
  intro c hc
  obtain ⟨c₁, hc₁, K₁, hSW⟩ := siegelWalfisz (2 * c) (by positivity)
  obtain ⟨K₂, hK₂, h₂⟩ := BV.log_rpow_le_sqrt (2 * c)
  obtain ⟨K₄, hK₄, h₄⟩ := BV.log_rpow_le_sqrt (2 * c + 1)
  obtain ⟨K₃, hK₃, h₃⟩ := BV.exp_neg_sqrt_log_le c₁ hc₁ (2 * c)
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  set C := (Real.log 4 + 5) * (1 + Real.exp 2) * K₂ + max K₁ 0 * K₃ * 2 ^ (2 * c) + 2 * K₄
    with hCdef
  refine ⟨C, fun x hx q hq hqx a ha y hy0 hyx ↦ ?_⟩
  rw [one_mul]
  have hx2 : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  set L := Real.log x with hLdef
  have hL : 0 < L := Real.log_pos (by linarith)
  have hL2c : 0 < L ^ (2 * c) := Real.rpow_pos_of_pos hL _
  have hsx1 : 1 ≤ Real.sqrt x := by rw [Real.le_sqrt (by norm_num) hx0.le]; linarith
  have hφ : (1 : ℝ) ≤ (Nat.totient q : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.totient_pos.2 (by omega)).ne'
  have hθ := xi_theta_le_psi x hy0 hyx q a
  have hyφ0 : 0 ≤ y / (Nat.totient q : ℝ) := by positivity
  have hyφ : y / (Nat.totient q : ℝ) ≤ y := div_le_self hy0 hφ
  -- √x ≤ K₂ x / L^{2c}
  have hsq : Real.sqrt x ≤ K₂ * x / L ^ (2 * c) := by
    rw [le_div_iff₀ hL2c]
    have := h₂ x hx2
    have hs : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    nlinarith [Real.sqrt_nonneg x]
  have hm0 : 0 ≤ max K₁ 0 := le_max_right _ _
  have hC1 : 0 ≤ max K₁ 0 * K₃ * 2 ^ (2 * c) * x / L ^ (2 * c) := by positivity
  have hC2 : 0 ≤ 2 * K₄ * x / L ^ (2 * c) := by positivity
  have hC3 : 0 ≤ (Real.log 4 + 5) * (1 + Real.exp 2) * K₂ * x / L ^ (2 * c) := by positivity
  have hCsplit : C * x / L ^ (2 * c) = (Real.log 4 + 5) * (1 + Real.exp 2) * K₂ * x / L ^ (2 * c) +
      max K₁ 0 * K₃ * 2 ^ (2 * c) * x / L ^ (2 * c) + 2 * K₄ * x / L ^ (2 * c) := by
    rw [hCdef]; ring
  rw [hCsplit]
  by_cases hbig : Real.sqrt x ≤ y ∧ Real.exp 2 ≤ y
  · obtain ⟨hy1, hy2⟩ := hbig
    have hy2' : (2 : ℝ) ≤ y := le_trans (by have := Real.add_one_le_exp (2 : ℝ); linarith) hy2
    have hy0' : 0 < y := by linarith
    have hly2 : 2 ≤ Real.log y := by rw [Real.le_log_iff_exp_le hy0']; exact hy2
    have hlsx : Real.log (Real.sqrt x) = L / 2 := by
      rw [Real.log_sqrt hx0.le]
    have hlyL : L / 2 ≤ Real.log y := by
      rw [← hlsx]; exact Real.log_le_log (by positivity) hy1
    -- q ≤ (log y)^{2c}
    have hqy : (q : ℝ) ≤ Real.log y ^ (2 * c) := by
      have h1 : L ≤ Real.log y ^ 2 := by nlinarith
      calc (q : ℝ) ≤ L ^ c := hqx
        _ ≤ (Real.log y ^ 2) ^ c := Real.rpow_le_rpow hL.le h1 hc.le
        _ = Real.log y ^ (2 * c) := rpow_two_mul_eq (by linarith)
    have hsw := hSW y hy2' q a hq ha hqy
    -- √x ≥ 2
    have hsx2 : 2 ≤ Real.sqrt x := by
      rw [Real.le_sqrt (by norm_num) hx0.le]
      have hex : Real.exp 2 ≤ x := hy2.trans hyx
      have he : (4 : ℝ) ≤ Real.exp 2 := by
        have h := Real.add_one_le_exp (1 : ℝ)
        have e2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        nlinarith
      nlinarith
    have hexp : Real.exp (-c₁ * Real.sqrt (Real.log y)) ≤
        K₃ * 2 ^ (2 * c) / L ^ (2 * c) := by
      have h1 : Real.exp (-c₁ * Real.sqrt (Real.log y)) ≤
          Real.exp (-c₁ * Real.sqrt (Real.log (Real.sqrt x))) := by
        apply Real.exp_le_exp.mpr
        have : Real.sqrt (Real.log (Real.sqrt x)) ≤ Real.sqrt (Real.log y) :=
          Real.sqrt_le_sqrt (by rw [hlsx]; exact hlyL)
        nlinarith
      refine h1.trans ((h₃ _ hsx2).trans (le_of_eq ?_))
      rw [hlsx, Real.div_rpow hL.le (by norm_num)]
      field_simp
    have hA : |HeathBrown1985.psi y q a - y / (Nat.totient q : ℝ)| ≤
        max K₁ 0 * K₃ * 2 ^ (2 * c) * x / L ^ (2 * c) := by
      refine hsw.trans ?_
      have hK : K₁ * y ≤ max K₁ 0 * x := by
        have := mul_le_mul_of_nonneg_left hyx hm0
        have := mul_le_mul_of_nonneg_right (le_max_left K₁ 0) hy0
        linarith
      have hE0 : 0 ≤ Real.exp (-c₁ * Real.sqrt (Real.log y)) := (Real.exp_pos _).le
      calc K₁ * y * Real.exp (-c₁ * Real.sqrt (Real.log y))
          ≤ max K₁ 0 * x * Real.exp (-c₁ * Real.sqrt (Real.log y)) :=
            mul_le_mul_of_nonneg_right hK hE0
        _ ≤ max K₁ 0 * x * (K₃ * 2 ^ (2 * c) / L ^ (2 * c)) := by gcongr
        _ = _ := by ring
    have hB : |Xi2012.theta (Xi2012.primesUpTo x) y q a - HeathBrown1985.psi y q a| ≤
        2 * K₄ * x / L ^ (2 * c) := by
      obtain ⟨h1, h2⟩ := psi_sub_xi_theta x hy0 hyx q a
      rw [abs_sub_comm, abs_of_nonneg h1]
      refine h2.trans ?_
      have h3 : Chebyshev.psi y - Chebyshev.theta y ≤ 2 * Real.sqrt y * Real.log y :=
        (le_abs_self _).trans (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith))
      have h4 : 2 * Real.sqrt y * Real.log y ≤ 2 * Real.sqrt x * L := by
        have := Real.sqrt_le_sqrt hyx
        have := Real.log_le_log hy0' hyx
        have := Real.sqrt_nonneg y
        nlinarith
      have h5 : Real.sqrt x * L ≤ K₄ * x / L ^ (2 * c) := by
        rw [le_div_iff₀ hL2c]
        have h6 := h₄ x hx2
        rw [Real.rpow_add hL, Real.rpow_one] at h6
        have hs : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
        nlinarith [Real.sqrt_nonneg x]
      have : 2 * Real.sqrt x * L ≤ 2 * K₄ * x / L ^ (2 * c) := by
        have h7 := mul_le_mul_of_nonneg_left h5 (by norm_num : (0 : ℝ) ≤ 2)
        calc 2 * Real.sqrt x * L = 2 * (Real.sqrt x * L) := by ring
          _ ≤ 2 * (K₄ * x / L ^ (2 * c)) := h7
          _ = 2 * K₄ * x / L ^ (2 * c) := by ring
      linarith
    calc |Xi2012.theta (Xi2012.primesUpTo x) y q a - y / (Nat.totient q : ℝ)|
        ≤ |Xi2012.theta (Xi2012.primesUpTo x) y q a - HeathBrown1985.psi y q a| +
          |HeathBrown1985.psi y q a - y / (Nat.totient q : ℝ)| := abs_sub_le _ _ _
      _ ≤ 2 * K₄ * x / L ^ (2 * c) + max K₁ 0 * K₃ * 2 ^ (2 * c) * x / L ^ (2 * c) := add_le_add hB hA
      _ ≤ _ := by linarith
  · -- small y
    have hysmall : y ≤ (1 + Real.exp 2) * Real.sqrt x := by
      rcases not_and_or.mp hbig with h | h
      · push_neg at h; nlinarith [Real.exp_pos 2]
      · push_neg at h; nlinarith [Real.exp_pos 2]
    have hpsi : Chebyshev.psi y ≤ (Real.log 4 + 4) * y := Chebyshev.psi_le_const_mul_self hy0
    have h1 : |Xi2012.theta (Xi2012.primesUpTo x) y q a - y / (Nat.totient q : ℝ)| ≤
        (Real.log 4 + 5) * y := by
      rw [abs_le]; constructor <;> nlinarith [hθ.1, hθ.2]
    have h2 : (Real.log 4 + 5) * y ≤ (Real.log 4 + 5) * (1 + Real.exp 2) * K₂ * x / L ^ (2 * c) := by
      have h3 : (Real.log 4 + 5) * y ≤ (Real.log 4 + 5) * ((1 + Real.exp 2) * Real.sqrt x) :=
        mul_le_mul_of_nonneg_left hysmall (by linarith)
      have h4 : (Real.log 4 + 5) * ((1 + Real.exp 2) * Real.sqrt x) ≤
          (Real.log 4 + 5) * ((1 + Real.exp 2) * (K₂ * x / L ^ (2 * c))) := by
        gcongr
      calc _ ≤ _ := h3.trans h4
        _ = _ := by ring
    linarith

/-- Xi's remark: Theorem 2 at any `c₀ > 0` gives the classical log power saving.
CONDITIONAL ON `Xi2012.Theorem2At c₀` only. -/
theorem xi_classical_of_theorem2 {c₀ : ℝ} (hc : 0 < c₀) (h : Xi2012.Theorem2At c₀) :
    Xi2012.ClassicalLogSaving :=
  Xi2012.classical_of_theorem2 hc h xi_siegelWalfisz

end LeanLab.PNTPort.PsiChi
