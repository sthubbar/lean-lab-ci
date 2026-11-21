/-
AI wrote the Lean code. CLAUDE prep1121 Song-fourier, 2026-11-21.
Source: Song 2020, https://arxiv.org/pdf/2012.06322v1, printed pages 3 to 5, S2 on page 4 and the top of page 5,
Lemma 1 and the S2 displays of the proof of Lemma 4.
Split of the route step `Decomp139.fourier_approximation` into leaves.
The coefficient family comes from the proved `song_lemma1_majorant591`, set to zero
outside the range |h| at most H. The S2 argument of page 5 is then cut into a pointwise
majorant bound, the passage from primes to integers, the expansion of the majorant,
the conjugation symmetry, partial summation, the exponent pair (1/2, 1/2) input of
Graham and Kolesnik display 3.3.4, the frequency zero term and the final arithmetic.
The theorem `fourier_approximation_of_leaves` at the end proves the exact statement
of `Decomp139.fourier_approximation` from these leaves; no existing file is changed.
Binary Goldbach is open.
-/
import LeanLab.Song2020.Decomp139
import LeanLab.Song2020.Repair591FourierMajorant

namespace LeanLab.Song2020.Prep1121FourierS2

open LeanLab.Song2020 LeanLab.Song2020.State1562 LeanLab.Song2020.Decomp139
open scoped Classical

noncomputable section

/-! ## Elementary facts about `eC` -/

theorem norm_eC (x : ℝ) : ‖eC x‖ = 1 := by
  unfold eC
  have h : (2 * Real.pi * Complex.I * x : ℂ) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

theorem eC_neg (x : ℝ) : eC (-x) = (starRingEnd ℂ) (eC x) := by
  unfold eC
  rw [← Complex.exp_conj]
  congr 1
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_cast, Complex.conj_ofReal]
  simp [Complex.conj_ofReal, h2]

/-! ## Leaves and proved steps -/

/-- PROVED STEP: Song 2020, page 4, display defining S1 plus S2, and page 3, Lemma 1.
The sawtooth difference minus its truncation is the difference of the two values of
psi double prime, and a pointwise real majorant M of psi double prime bounds S2 by the
weighted sum of M at both points. PROVED here. -/
theorem s2_pointwise_majorant (γ : ℝ) (hγ : 0 < γ) (n : ℕ) (y α : ℝ)
    (a : ℕ → ℤ → ℂ) (H : ℕ) (M : ℝ → ℝ)
    (hM : ∀ x : ℝ, ‖((saw x : ℝ) : ℂ) - Decomp139.fourier a H x‖ ≤ M x) :
    ‖sawSum γ n y α - truncatedSum a H γ n y α‖ ≤
      ∑ p ∈ windowPrimes n y,
        psWeight γ p * (M (-((p : ℝ) + 1) ^ γ) + M (-(p : ℝ) ^ γ)) := by
  unfold sawSum truncatedSum
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  have hw : 0 ≤ psWeight γ p := by
    unfold psWeight
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have heq : (psWeight γ p : ℂ) * eC (α * p) *
        ((saw (-((p : ℝ) + 1) ^ γ) - saw (-(p : ℝ) ^ γ) : ℝ) : ℂ) -
      (psWeight γ p : ℂ) * eC (α * p) *
        (fourier a H (-((p : ℝ) + 1) ^ γ) - fourier a H (-(p : ℝ) ^ γ)) =
      (psWeight γ p : ℂ) * eC (α * p) *
        ((((saw (-((p : ℝ) + 1) ^ γ) : ℝ) : ℂ) - fourier a H (-((p : ℝ) + 1) ^ γ)) -
          (((saw (-(p : ℝ) ^ γ) : ℝ) : ℂ) - fourier a H (-(p : ℝ) ^ γ))) := by
    push_cast; ring
  rw [heq, norm_mul, norm_mul, norm_eC, Complex.norm_real, Real.norm_of_nonneg hw, mul_one]
  refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add (hM _) (hM _))) hw

/-- PROVED STEP: Song 2020, page 4, display after "By Lemma 3.1, we have", the passage from the primes of the window
to all integers of the window, valid because the summand is nonnegative. PROVED here. -/
theorem primes_to_window (n : ℕ) (y : ℝ) (F : ℕ → ℝ) (hF : ∀ x, 0 ≤ F x) :
    ∑ p ∈ windowPrimes n y, F p ≤
      ∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
        (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y), F x := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x _ _ => hF x)
  intro x hx
  unfold windowPrimes at hx
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hx.2.2⟩

/-- PROVED STEP: Song 2020, page 4, display after "By Lemma 3.1, we have", expansion of the majorant of Lemma 1:
the weighted sum of the real majorant is at most the coefficient bound times the sum over
|h| at most H of the exponential sums. PROVED here. -/
theorem majorant_expand (S : Finset ℕ) (w : ℕ → ℝ) (φ : ℕ → ℝ) (b : ℤ → ℂ) (H : ℕ)
    (B : ℝ) (hb : ∀ h ∈ Finset.Icc (-(H : ℤ)) H, ‖b h‖ ≤ B) :
    ∑ x ∈ S, w x * (∑ h ∈ Finset.Icc (-(H : ℤ)) H, b h * eC (φ x * h)).re ≤
      B * ∑ h ∈ Finset.Icc (-(H : ℤ)) H,
        ‖∑ x ∈ S, (w x : ℂ) * eC (φ x * h)‖ := by
  have h1 : ∑ x ∈ S, w x * (∑ h ∈ Finset.Icc (-(H : ℤ)) H, b h * eC (φ x * h)).re =
      (∑ h ∈ Finset.Icc (-(H : ℤ)) H, b h * ∑ x ∈ S, (w x : ℂ) * eC (φ x * h)).re := by
    have hc : (∑ h ∈ Finset.Icc (-(H : ℤ)) H, b h * ∑ x ∈ S, (w x : ℂ) * eC (φ x * h)) =
        ∑ x ∈ S, (w x : ℂ) * ∑ h ∈ Finset.Icc (-(H : ℤ)) H, b h * eC (φ x * h) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro h _
      ring
    rw [hc, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [Complex.re_ofReal_mul]
  rw [h1, Finset.mul_sum]
  refine (Complex.re_le_norm _).trans ((norm_sum_le _ _).trans (Finset.sum_le_sum fun h hh => ?_))
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hb h hh) (norm_nonneg _)

/-- PROVED STEP: Song 2020, page 4, display after "By Lemma 3.1, we have", the reduction to positive frequencies
1 at most h at most H: with real weights, the frequency h at the point minus u has the same
modulus as the frequency |h| at the point u, by complex conjugation. PROVED here. -/
theorem conj_phase (S : Finset ℕ) (w u : ℕ → ℝ) (h : ℤ) :
    ‖∑ x ∈ S, (w x : ℂ) * eC (-(u x) * h)‖ =
      ‖∑ x ∈ S, (w x : ℂ) * eC (((h.natAbs : ℕ) : ℝ) * u x)‖ := by
  rcases le_or_gt 0 h with h0 | h0
  · have hc : ((h.natAbs : ℕ) : ℝ) = (h : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast h0)]
    have : ∑ x ∈ S, (w x : ℂ) * eC (-(u x) * h) =
        (starRingEnd ℂ) (∑ x ∈ S, (w x : ℂ) * eC (((h.natAbs : ℕ) : ℝ) * u x)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [map_mul, Complex.conj_ofReal, ← eC_neg, hc]
      congr 2; ring
    rw [this, Complex.norm_conj]
  · have hc : ((h.natAbs : ℕ) : ℝ) = -(h : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast h0)]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hc]; congr 2; ring

/-- LEAF: Song 2020, page 4, display after "Partial summation yields":
the weighted window sum with the weight psWeight, at most 1/γ times n to the 1 minus γ,
is at most 2/γ times n to the 1 minus γ times any bound B on the exponential sums over the
initial segments of the window. Route: RouteS1Abel.norm_window_sum_mul_le with the weight
truncated beyond n, plus the telescoping total variation of the increasing weight. -/
theorem weighted_window_bound (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (n : ℕ) (hn : 3 ≤ n)
    (y : ℝ) (hy : y ≤ (n : ℝ) / 3) (f : ℕ → ℝ) (B : ℝ)
    (hB : ∀ t : ℝ, ‖∑ x ∈ subWindow n y t, eC (f x)‖ ≤ B) :
    ‖∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
        (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y), (psWeight γ x : ℂ) * eC (f x)‖ ≤
      2 / γ * (n : ℝ) ^ (1 - γ) * B := by
  sorry

/-- LEAF: Song 2020, page 4, last display, "Using the exponent pair (1/2, 1/2)
([2], eqn. 3.3.4)": the unweighted sum of e of k x to the γ over any initial segment of the
window is at most a constant times k to the 1/2 times n to the γ/2, plus k to the minus 1
times n to the 1 minus γ, both for the points x and x plus 1. CITED, Graham and Kolesnik
display 3.3.4; route through the ported BakerHarmanPintz1997.PortedVanDerCorput
second derivative test and Kusmin Landau inequality, over dyadic blocks. -/
theorem exponent_pair_half (γ : ℝ) (hγ : 44 / 45 < γ) (hγ1 : γ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ, y ≤ (n : ℝ) / 3 →
      ∀ t : ℝ, ∀ k : ℕ, 1 ≤ k →
        ‖∑ x ∈ subWindow n y t, eC ((k : ℝ) * (x : ℝ) ^ γ)‖ ≤
            C * ((k : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2) +
              (k : ℝ)⁻¹ * (n : ℝ) ^ (1 - γ)) ∧
        ‖∑ x ∈ subWindow n y t, eC ((k : ℝ) * ((x : ℝ) + 1) ^ γ)‖ ≤
            C * ((k : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2) +
              (k : ℝ)⁻¹ * (n : ℝ) ^ (1 - γ)) := by
  sorry

/-- PROVED STEP: Song 2020, page 4, display after "By Lemma 3.1, we have", the frequency h = 0 term
H to the minus 1 times y times n to the 1 minus γ: the weighted count of the window is at
most 1/γ times n to the 1 minus γ times 2y plus 1. -/
theorem zero_frequency_term (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (n : ℕ) (hn : 3 ≤ n)
    (y : ℝ) (hy0 : 0 ≤ y) (hy : y ≤ (n : ℝ) / 3) (φ : ℕ → ℝ) :
    ‖∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
        (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y),
        (psWeight γ x : ℂ) * eC (φ x * ((0 : ℤ) : ℝ))‖ ≤
      1 / γ * (n : ℝ) ^ (1 - γ) * (2 * y + 1) := by
  have hsimp : ∀ x : ℕ, (psWeight γ x : ℂ) * eC (φ x * ((0 : ℤ) : ℝ)) =
      (psWeight γ x : ℂ) := by
    intro x; simp [eC]
  simp only [hsimp]
  refine (norm_sum_le _ _).trans ?_
  set S := (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
    (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y) with hS
  set A := Nat.ceil ((n : ℝ) / 3 - y) with hAdef
  set m := Nat.floor (2 * y) with hmdef
  have hAr : (n : ℝ) / 3 - y ≤ A := Nat.le_ceil _
  have hsub : S ⊆ Finset.Icc A (A + m) := by
    intro x hx
    rw [hS, Finset.mem_filter, abs_lt] at hx
    obtain ⟨_, h1, h2⟩ := hx
    have hA : A ≤ x := Nat.ceil_le.mpr (by linarith)
    have hm : x - A ≤ m := by
      apply Nat.le_floor
      rw [Nat.cast_sub hA]
      linarith
    exact Finset.mem_Icc.mpr ⟨hA, by omega⟩
  have hcard : (S.card : ℝ) ≤ 2 * y + 1 := by
    have h1 : S.card ≤ m + 1 := by
      have := Finset.card_le_card hsub
      rw [Nat.card_Icc] at this
      omega
    have h2 : (m : ℝ) ≤ 2 * y := Nat.floor_le (by positivity)
    have h3 : (S.card : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast h1
    linarith
  have hw : ∀ x ∈ S, ‖(psWeight γ x : ℂ)‖ ≤ 1 / γ * (n : ℝ) ^ (1 - γ) := by
    intro x hx
    rw [hS, Finset.mem_filter, abs_lt] at hx
    obtain ⟨_, _, h2⟩ := hx
    have hxn : (x : ℝ) ≤ n := by linarith
    rw [Complex.norm_real, Real.norm_of_nonneg (by
      unfold psWeight
      exact mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _))]
    unfold psWeight
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hxn (by linarith)) (by positivity)
  have hB0 : 0 ≤ 1 / γ * (n : ℝ) ^ (1 - γ) := by positivity
  calc ∑ x ∈ S, ‖(psWeight γ x : ℂ)‖ ≤ S.card • (1 / γ * (n : ℝ) ^ (1 - γ)) :=
        Finset.sum_le_card_nsmul _ _ _ hw
    _ = (S.card : ℝ) * (1 / γ * (n : ℝ) ^ (1 - γ)) := nsmul_eq_mul _ _
    _ ≤ (2 * y + 1) * (1 / γ * (n : ℝ) ^ (1 - γ)) :=
        mul_le_mul_of_nonneg_right hcard hB0
    _ = 1 / γ * (n : ℝ) ^ (1 - γ) * (2 * y + 1) := by ring

/-- PROVED STEP: Song 2020, page 4, display after "By Lemma 3.1, we have", the sum over |h| at most H split into the
term h = 0 and the 2H nonzero frequencies. PROVED here. -/
theorem sum_Icc_split (H : ℕ) (g : ℤ → ℝ) (G : ℝ)
    (hg : ∀ h ∈ Finset.Icc (-(H : ℤ)) H, h ≠ 0 → g h ≤ G) :
    ∑ h ∈ Finset.Icc (-(H : ℤ)) H, g h ≤ g 0 + 2 * H * G := by
  have h0 : (0 : ℤ) ∈ Finset.Icc (-(H : ℤ)) H := by simp
  rw [← Finset.add_sum_erase _ _ h0]
  refine add_le_add le_rfl ?_
  have hcard : ((Finset.Icc (-(H : ℤ)) H).erase 0).card = 2 * H := by
    rw [Finset.card_erase_of_mem h0, Int.card_Icc]
    omega
  calc ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).erase 0, g h
      ≤ ∑ _h ∈ (Finset.Icc (-(H : ℤ)) H).erase 0, G :=
        Finset.sum_le_sum fun h hh =>
          hg h (Finset.mem_of_mem_erase hh) (Finset.ne_of_mem_erase hh)
    _ = 2 * H * G := by rw [Finset.sum_const, hcard, nsmul_eq_mul]; push_cast; ring

/-- PROVED STEP: Song 2020, page 5, the display "Concluding the above estimate": the final
arithmetic. With the trivial bounds |h| to the 1/2 at most H to the 1/2 and |h| inverse at
most 1 per frequency, the two majorant sums are at most an explicit constant times
H to the 1/2 times n to the 1 minus γ/2 plus H inverse times y times n to the 1 minus γ.
It uses n to the 2 minus 2γ at most n to the 1 minus γ/2 and 2y plus 1 at most 3y. -/
theorem s2_final_arith (γ : ℝ) (hγ : 44 / 45 < γ) (hγ1 : γ < 1) (C0 CE : ℝ)
    (hC0 : 0 ≤ C0) (hCE : 0 ≤ CE) (n : ℕ) (hn : 1 ≤ n) (y : ℝ) (hy : 1 ≤ y)
    (H : ℕ) (hH : 1 ≤ H) :
    2 * (C0 / H * (1 / γ * (n : ℝ) ^ (1 - γ) * (2 * y + 1) +
      2 * H * (2 / γ * (n : ℝ) ^ (1 - γ) *
        (CE * ((H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2) + (n : ℝ) ^ (1 - γ)))))) ≤
      (6 * C0 / γ + 16 * C0 * CE / γ) * tailBudget γ n y H := by
  have hγ0 : 0 < γ := by linarith
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  set P := (n : ℝ) ^ (1 - γ) with hP
  set Q := (n : ℝ) ^ (γ / 2) with hQ
  set R := (H : ℝ) ^ ((1 : ℝ) / 2) with hR
  have hP0 : 0 ≤ P := Real.rpow_nonneg hnpos.le _
  have hQ0 : 0 ≤ Q := Real.rpow_nonneg hnpos.le _
  have hPQ : P ≤ Q := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hR1 : 1 ≤ R := Real.one_le_rpow hHr (by norm_num)
  have hsplit : (n : ℝ) ^ (1 - γ / 2) = P * Q := by
    rw [hP, hQ, ← Real.rpow_add hnpos]; congr 1; ring
  unfold tailBudget
  rw [hsplit]
  have hHpos : (0 : ℝ) < H := by linarith
  have e1 : 2 * (C0 / H * (1 / γ * P * (2 * y + 1) +
      2 * H * (2 / γ * P * (CE * (R * Q + P))))) =
      (2 * C0 * P * (2 * y + 1) / γ) / H + 8 * C0 * CE * P * (R * Q + P) / γ := by
    field_simp; ring
  have e2 : (6 * C0 / γ + 16 * C0 * CE / γ) * (R * (P * Q) + (H : ℝ)⁻¹ * y * P) =
      (6 * C0 * y * P / γ) / H + 16 * C0 * CE * R * P * Q / γ +
        (6 * C0 / γ) * (R * (P * Q)) + 16 * C0 * CE / γ * ((H : ℝ)⁻¹ * y * P) := by
    field_simp; ring
  rw [e1, e2]
  have t1 : (2 * C0 * P * (2 * y + 1) / γ) / H ≤ (6 * C0 * y * P / γ) / H := by
    apply div_le_div_of_nonneg_right _ hHpos.le
    apply div_le_div_of_nonneg_right _ hγ0.le
    nlinarith [mul_nonneg (mul_nonneg hC0 hP0) (sub_nonneg.mpr hy)]
  have t2 : 8 * C0 * CE * P * (R * Q + P) / γ ≤ 16 * C0 * CE * R * P * Q / γ := by
    apply div_le_div_of_nonneg_right _ hγ0.le
    have h1 : R * Q + P ≤ 2 * (R * Q) := by
      nlinarith [mul_le_mul_of_nonneg_right hR1 hQ0]
    have hc : 0 ≤ 8 * C0 * CE * P := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 hc]
  have t3 : 0 ≤ (6 * C0 / γ) * (R * (P * Q)) := by positivity
  have t4 : 0 ≤ 16 * C0 * CE / γ * ((H : ℝ)⁻¹ * y * P) := by positivity
  linarith

/-! ## Proved glue -/

/-- CONDITIONAL ON weighted_window_bound. Proved from the leaves. Page 4, the per frequency bound for h nonzero. -/
theorem per_h_bound (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (n : ℕ) (hn : 3 ≤ n)
    (y : ℝ) (hy : y ≤ (n : ℝ) / 3) (H : ℕ) (v : ℕ → ℝ) (CE : ℝ) (hCE : 0 ≤ CE)
    (hv : ∀ t : ℝ, ∀ k : ℕ, 1 ≤ k →
      ‖∑ x ∈ subWindow n y t, eC ((k : ℝ) * v x)‖ ≤
        CE * ((k : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2) + (k : ℝ)⁻¹ * (n : ℝ) ^ (1 - γ)))
    (h : ℤ) (hh : h ∈ Finset.Icc (-(H : ℤ)) H) (h0 : h ≠ 0) :
    ‖∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
        (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y),
        (psWeight γ x : ℂ) * eC (-(v x) * h)‖ ≤
      2 / γ * (n : ℝ) ^ (1 - γ) *
        (CE * ((H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2) + (n : ℝ) ^ (1 - γ))) := by
  rw [conj_phase]
  set k := h.natAbs with hk
  have hk1 : 1 ≤ k := by rw [hk]; exact Int.natAbs_pos.mpr h0
  have hkH : k ≤ H := by
    rw [Finset.mem_Icc] at hh; rw [hk]; omega
  have hB := weighted_window_bound γ hγ0 hγ1 n hn y hy (fun x => (k : ℝ) * v x) _
    (fun t => hv t k hk1)
  refine hB.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  refine mul_le_mul_of_nonneg_left ?_ hCE
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hkHR : (k : ℝ) ≤ H := by exact_mod_cast hkH
  have hnp : 0 ≤ (n : ℝ) ^ (γ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hnq : 0 ≤ (n : ℝ) ^ (1 - γ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine add_le_add (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (by linarith) hkHR (by norm_num)) hnp) ?_
  have : (k : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hkR
  calc (k : ℝ)⁻¹ * (n : ℝ) ^ (1 - γ) ≤ 1 * (n : ℝ) ^ (1 - γ) :=
        mul_le_mul_of_nonneg_right this hnq
    _ = (n : ℝ) ^ (1 - γ) := one_mul _

/-- CONDITIONAL ON weighted_window_bound. Proved from the leaves. Page 4, the bound of one of the two majorant sums. -/
theorem majorant_sum_bound (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (n : ℕ) (hn : 3 ≤ n)
    (y : ℝ) (hy0 : 0 ≤ y) (hy : y ≤ (n : ℝ) / 3) (H : ℕ) (b : ℤ → ℂ) (C0 : ℝ)
    (hb : ∀ h ∈ Finset.Icc (-(H : ℤ)) H, ‖b h‖ ≤ C0 / H) (hC0 : 0 ≤ C0)
    (v : ℕ → ℝ) (CE : ℝ) (hCE : 0 ≤ CE)
    (hv : ∀ t : ℝ, ∀ k : ℕ, 1 ≤ k →
      ‖∑ x ∈ subWindow n y t, eC ((k : ℝ) * v x)‖ ≤
        CE * ((k : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2) + (k : ℝ)⁻¹ * (n : ℝ) ^ (1 - γ))) :
    ∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
        (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y),
        psWeight γ x * (∑ h ∈ Finset.Icc (-(H : ℤ)) H, b h * eC (-(v x) * h)).re ≤
      C0 / H * (1 / γ * (n : ℝ) ^ (1 - γ) * (2 * y + 1) +
        2 * H * (2 / γ * (n : ℝ) ^ (1 - γ) *
          (CE * ((H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2) + (n : ℝ) ^ (1 - γ))))) := by
  refine (majorant_expand _ (psWeight γ) (fun x => -(v x)) b H (C0 / H) hb).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (sum_Icc_split H _ _ fun h hh h0 =>
    per_h_bound γ hγ0 hγ1 n hn y hy H v CE hCE hv h hh h0).trans ?_
  exact add_le_add (zero_frequency_term γ hγ0 hγ1 n hn y hy0 hy _) le_rfl

/-- CONDITIONAL ON weighted_window_bound and exponent_pair_half. Proved from the leaves, with no sorry of its own. The exact statement of
`Decomp139.fourier_approximation`, Song 2020 pages 4 and 5, the S2 bound. -/
theorem fourier_approximation_of_leaves :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 →
      ∃ a : ℕ → ℤ → ℂ, ∃ K : ℝ, 1 ≤ K ∧
        (∀ H : ℕ, ∀ h : ℤ, h ≠ 0 → ‖a H h‖ ≤ K / |(h : ℝ)|) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
          (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 →
          ∀ H : ℕ, 1 ≤ H → ∀ α : ℝ,
            ‖sawSum γ n y α - truncatedSum a H γ n y α‖ ≤
              C * tailBudget γ n y H := by
  intro γ hγ hγ1
  have hγ0 : 0 < γ := by linarith
  obtain ⟨C0, hC0, a, b, hab⟩ := Repair591FourierMajorant.song_lemma1_majorant591
  obtain ⟨CE, hCE, NE, hNE⟩ := exponent_pair_half γ hγ hγ1
  refine ⟨fun H h => if |h| ≤ (H : ℤ) then a H h else 0, C0 + 1, by linarith, ?_, ?_⟩
  · intro H h h0
    have hpos : 0 < |(h : ℝ)| := abs_pos.mpr (by exact_mod_cast h0)
    by_cases hh : |h| ≤ (H : ℤ)
    · by_cases hH : 1 ≤ H
      · simp only [hh, ite_true]
        refine ((hab H hH).1 h h0 hh).trans ?_
        exact div_le_div_of_nonneg_right (by linarith) hpos.le
      · have : H = 0 := by omega
        subst this
        exfalso; apply h0; simp at hh; omega
    · simp only [hh, ite_false, norm_zero]
      positivity
  refine ⟨6 * C0 / γ + 16 * C0 * CE / γ, by positivity, max NE 3, ?_⟩
  intro n hn y hy hy3 H hH α
  have hn3 : 3 ≤ n := le_of_max_le_right hn
  have hnE : NE ≤ n := le_of_max_le_left hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hexp : 0 ≤ songExponent γ := by unfold songExponent; linarith
  have hy1 : 1 ≤ y := (Real.one_le_rpow hn1 hexp).trans hy.le
  set M : ℝ → ℝ := fun x => (∑ h ∈ Finset.Icc (-(H : ℤ)) H, b H h * eC (x * h)).re with hMdef
  have hM : ∀ x : ℝ, ‖((saw x : ℝ) : ℂ) -
      Decomp139.fourier (fun H h => if |h| ≤ (H : ℤ) then a H h else 0) H x‖ ≤ M x := by
    intro x
    have hf : Decomp139.fourier (fun H h => if |h| ≤ (H : ℤ) then a H h else 0) H x =
        ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h => h ≠ 0), a H h * eC (x * h) := by
      unfold Decomp139.fourier
      refine Finset.sum_congr rfl fun h hh => ?_
      have hh' : |h| ≤ (H : ℤ) := by
        rw [Finset.mem_filter, Finset.mem_Icc] at hh
        exact abs_le.mpr hh.1
      simp only [hh', ite_true, mul_comm (h : ℝ) x]
    rw [hf]
    exact ((hab H hH).2.2 x).2
  have hM0 : ∀ x, 0 ≤ M x := fun x => (norm_nonneg _).trans (hM x)
  have hw0 : ∀ x : ℕ, 0 ≤ psWeight γ x := fun x => by
    unfold psWeight
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hbH : ∀ h ∈ Finset.Icc (-(H : ℤ)) H, ‖b H h‖ ≤ C0 / H := by
    intro h hh
    rw [Finset.mem_Icc] at hh
    exact (hab H hH).2.1 h (abs_le.mpr hh)
  have hy0 : 0 ≤ y := by linarith
  have hE := hNE n hnE y hy3
  have hA := majorant_sum_bound γ hγ0 hγ1 n hn3 y hy0 hy3 H (b H) C0 hbH hC0
    (fun x => ((x : ℝ) + 1) ^ γ) CE hCE (fun t k hk => (hE t k hk).2)
  have hB := majorant_sum_bound γ hγ0 hγ1 n hn3 y hy0 hy3 H (b H) C0 hbH hC0
    (fun x => (x : ℝ) ^ γ) CE hCE (fun t k hk => (hE t k hk).1)
  refine (s2_pointwise_majorant γ hγ0 n y α _ H M hM).trans ?_
  refine (primes_to_window n y _ fun x =>
    mul_nonneg (hw0 x) (add_nonneg (hM0 _) (hM0 _))).trans ?_
  refine le_trans ?_ (s2_final_arith γ hγ hγ1 C0 CE hC0 hCE n (by omega) y hy1 H hH)
  have hsum : ∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
        (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y),
        psWeight γ x * (M (-((x : ℝ) + 1) ^ γ) + M (-(x : ℝ) ^ γ)) =
      ∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
        (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y), psWeight γ x * M (-((x : ℝ) + 1) ^ γ) +
      ∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
        (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y), psWeight γ x * M (-(x : ℝ) ^ γ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => mul_add _ _ _
  rw [hsum, two_mul]
  exact add_le_add hA hB

end

end LeanLab.Song2020.Prep1121FourierS2

#print axioms LeanLab.Song2020.Prep1121FourierS2.fourier_approximation_of_leaves
