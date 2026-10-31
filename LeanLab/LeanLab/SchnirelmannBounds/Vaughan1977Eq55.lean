/-
P0066 Vaughan 1977, (5.3) to (5.5), p. 104, read on the page image. Unit U-6852,
CLOUD MANUAL-M1, 2026-10-21, track T1.

(5.3) F(n) = Σ_{3≤p₁≤x-3} Σ_{x-p₁<p₂≤2x-p₁, p₁+p₂=n} log p₁, so Ψ(x) = Σ_n F(n); N(x) ≥ #{n : F(n) > 0};
(5.4) Hölder: Ψ(x) ≤ N(x)^{11/15} (Σ F(n)^{15/4})^{4/15}; Lemma 8: F(n) < 16Cx/(1.6 + log x) Π_{p|n,p>2}
(p-1)/(p-2); hence (5.5). This file PROVES (5.5) in the `≤` form from Lemma 8, with
G(x) = Σ_n F(n) Π_{p|n,p>2} ((p-1)/(p-2))^{11/4} concrete, `eq55_of_lemma8`.

AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import LeanLab.SchnirelmannBounds.Vaughan1977Lemma12

open Finset Real
open scoped Classical

namespace LeanLab.SchnirelmannBounds.Vaughan1977Eq55
open LeanLab.SchnirelmannConstant LeanLab.RieselVaughan1983 LeanLab.SchnirelmannBounds.Vaughan1977
  LeanLab.SchnirelmannBounds.Vaughan1977Sec6 LeanLab.SchnirelmannBounds.Vaughan1977Lemma10
  LeanLab.SchnirelmannBounds.Vaughan1977Lemma12

/-- The primes `3 ≤ p₁ ≤ x - 3`. -/
noncomputable def P1 (x : ℝ) : Finset ℕ := (Icc 3 ⌊x - 3⌋₊).filter Nat.Prime

/-- The `n` with `x < n ≤ 2x`. -/
noncomputable def Nset (x : ℝ) : Finset ℕ := Ioc ⌊x⌋₊ ⌊2 * x⌋₊

/-- (5.3): `F(n) = Σ_{p₁} log p₁` over `p₁ ∈ P1`, `p₁ < n`, `n - p₁` prime, for `n ∈ Nset`. -/
noncomputable def F (x : ℝ) (n : ℕ) : ℝ :=
  ∑ p₁ ∈ (P1 x).filter (fun p => p < n ∧ (n - p).Prime), Real.log p₁

/-- `Π_{p|n, p>2} (p-1)/(p-2)` as a real. -/
noncomputable def Pn (n : ℕ) : ℝ := (prodQ n : ℝ)

/-- `G(x) = Σ_n F(n) Π_{p|n,p>2} ((p-1)/(p-2))^{11/4}`. -/
noncomputable def G (x : ℝ) : ℝ := ∑ n ∈ Nset x, F x n * Pn n ^ (11 / 4 : ℝ)

theorem Pn_pos (n : ℕ) : 0 < Pn n := by
  unfold Pn prodQ; push_cast
  apply Finset.prod_pos; intro p hp
  simp only [oddPF, Finset.mem_filter] at hp
  have : (3 : ℝ) ≤ p := by exact_mod_cast hp.2.2.1
  apply div_pos <;> linarith

theorem F_nonneg (x : ℝ) (n : ℕ) : 0 ≤ F x n := by
  unfold F; apply Finset.sum_nonneg; intro p _; exact Real.log_natCast_nonneg p

/-- Ψ(x) = Σ_{n ∈ (x, 2x]} F(n). -/
theorem psi_eq (x : ℝ) (hx : 6 ≤ x) : Psi x = ∑ n ∈ Nset x, F x n := by
  unfold Psi F
  rw [show ((Icc 3 ⌊x - 3⌋₊).filter Nat.Prime) = P1 x from rfl]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro p₁ hp₁
  simp only [P1, Finset.mem_filter, Finset.mem_Icc] at hp₁
  have hp3 : (p₁ : ℝ) ≤ x - 3 := by
    have := Nat.floor_le (show (0 : ℝ) ≤ x - 3 by linarith)
    have h2 : (p₁ : ℝ) ≤ ⌊x - 3⌋₊ := by exact_mod_cast hp₁.1.2
    linarith
  -- both sides are log p₁ times a count
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  congr 1
  norm_cast
  apply Finset.card_bij (fun p₂ _ => p₂ + p₁)
  · intro p₂ hp₂
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp₂
    obtain ⟨⟨h1, h2⟩, hpr, hlt⟩ := hp₂
    have h2' : (p₂ : ℝ) ≤ 2 * x - p₁ := by
      have := Nat.floor_le (show (0 : ℝ) ≤ 2 * x - p₁ by linarith)
      have h2r : (p₂ : ℝ) ≤ ⌊2 * x - p₁⌋₊ := by exact_mod_cast h2
      linarith
    simp only [Finset.mem_filter, Nset, Finset.mem_Ioc]
    refine ⟨⟨?_, ?_⟩, by omega, by rwa [Nat.add_sub_cancel]⟩
    · rw [Nat.floor_lt (by linarith)]; push_cast; linarith
    · rw [Nat.le_floor_iff (by linarith)]; push_cast; linarith
  · intro a _ b _ h; simpa using h
  · intro n hn
    simp only [Finset.mem_filter, Nset, Finset.mem_Ioc] at hn
    obtain ⟨⟨h1, h2⟩, hlt, hpr⟩ := hn
    refine ⟨n - p₁, ?_, Nat.sub_add_cancel hlt.le⟩
    simp only [Finset.mem_filter, Finset.mem_Icc]
    rw [Nat.floor_lt (by linarith)] at h1
    rw [Nat.le_floor_iff (by linarith)] at h2
    have hc : ((n - p₁ : ℕ) : ℝ) = (n : ℝ) - p₁ := by rw [Nat.cast_sub hlt.le]
    refine ⟨⟨by omega, ?_⟩, hpr, ?_⟩
    · rw [Nat.le_floor_iff (by linarith), hc]; linarith
    · rw [hc]; linarith

/-- Lemma 8 applied to `F`: `F(n) ≤ 16Cx/(1.6 + log x) Π(n)` for `x ≥ 10^52`, `n ∈ Nset`. -/
theorem F_le {C : ℝ} (hC0 : 0 ≤ C) (h8 : Lemma8 C) (x : ℝ) (hx : 10 ^ 52 ≤ x) (n : ℕ)
    (hn : n ∈ Nset x) : F x n ≤ 16 * C * x / (1.6 + Real.log x) * Pn n := by
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hal : alpha x = 1.6 := by unfold alpha; rw [if_neg (by linarith)]
  simp only [Nset, Finset.mem_Ioc] at hn
  have hnx : x < n := (Nat.floor_lt hx0.le).mp hn.1
  set T := (P1 x).filter (fun p => p < n ∧ (n - p).Prime)
  by_cases hT : T = ∅
  · have : F x n = 0 := by unfold F; rw [show (P1 x).filter (fun p => p < n ∧ (n - p).Prime) = T from rfl, hT]; simp
    rw [this]; have := Pn_pos n; positivity
  obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hT
  simp only [T, P1, Finset.mem_filter, Finset.mem_Icc] at hp
  obtain ⟨⟨⟨hp3, hpx⟩, hpp⟩, hpn, hq⟩ := hp
  have hpxr : (p : ℝ) ≤ x - 3 := by
    have := Nat.floor_le (show (0 : ℝ) ≤ x - 3 by linarith)
    have h2 : (p : ℝ) ≤ ⌊x - 3⌋₊ := by exact_mod_cast hpx
    linarith
  -- n is even: p odd and n - p an odd prime
  have hq3 : 3 ≤ n - p := by
    have : (p : ℝ) + 3 < n := by linarith
    have : p + 3 < n := by exact_mod_cast this
    omega
  have hev : Even (n : ℤ) := by
    have h1 : Odd p := hpp.odd_of_ne_two (by omega)
    have h2 : Odd (n - p) := hq.odd_of_ne_two (by omega)
    have : Even n := by
      have := h1.add_odd h2
      rwa [Nat.add_sub_cancel' hpn.le] at this
    exact_mod_cast this
  have h8' := h8 x (by linarith) n hev (Or.inr (by exact_mod_cast hnx))
  rw [hal] at h8'
  simp only [Int.natAbs_natCast] at h8'
  -- F ≤ log x · R(n, x)
  have hFR : F x n ≤ Real.log x * Rc n x := by
    unfold F Rc
    calc ∑ p₁ ∈ (P1 x).filter (fun p => p < n ∧ (n - p).Prime), Real.log p₁
        ≤ ∑ p₁ ∈ (P1 x).filter (fun p => p < n ∧ (n - p).Prime), Real.log x := by
          apply Finset.sum_le_sum; intro q hq
          simp only [P1, Finset.mem_filter, Finset.mem_Icc] at hq
          have : (q : ℝ) ≤ x - 3 := by
            have := Nat.floor_le (show (0 : ℝ) ≤ x - 3 by linarith)
            have h2 : (q : ℝ) ≤ ⌊x - 3⌋₊ := by exact_mod_cast hq.1.1.2
            linarith
          exact Real.log_le_log (by have : (3 : ℝ) ≤ q := by exact_mod_cast hq.1.1.1
                                    linarith) (by linarith)
      _ = Real.log x * ((P1 x).filter (fun p => p < n ∧ (n - p).Prime)).card := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ Real.log x * ((Icc 1 ⌊x⌋₊).filter
            (fun p : ℕ => p.Prime ∧ Nat.Prime ((n : ℤ) - (p : ℤ)).natAbs)).card := by
          apply mul_le_mul_of_nonneg_left _ hL.le
          have hcard : ((P1 x).filter (fun p => p < n ∧ (n - p).Prime)).card ≤ ((Icc 1 ⌊x⌋₊).filter
              (fun p : ℕ => p.Prime ∧ Nat.Prime ((n : ℤ) - (p : ℤ)).natAbs)).card := by
            apply Finset.card_le_card
            intro q hq
            simp only [P1, Finset.mem_filter, Finset.mem_Icc] at hq
            rw [Finset.mem_filter, Finset.mem_Icc]
            obtain ⟨⟨⟨hq3, hqx⟩, hqp⟩, hqn, hqq⟩ := hq
            have hqxr : (q : ℝ) ≤ x := by
              have := Nat.floor_le (show (0 : ℝ) ≤ x - 3 by linarith)
              have h2 : (q : ℝ) ≤ ⌊x - 3⌋₊ := by exact_mod_cast hqx
              linarith
            refine ⟨⟨by omega, Nat.le_floor hqxr⟩, hqp, ?_⟩
            have : ((n : ℤ) - (q : ℤ)).natAbs = n - q := by omega
            rw [this]; exact hqq
          exact_mod_cast hcard
  have hP := Pn_pos n
  have e : 16 * C * x / ((1.6 + Real.log x) * Real.log x) * (prodQ n : ℝ) * Real.log x =
      16 * C * x / (1.6 + Real.log x) * Pn n := by
    unfold Pn; field_simp
  have := mul_lt_mul_of_pos_left h8' hL
  rw [mul_comm (Real.log x) (16 * C * x / ((1.6 + Real.log x) * Real.log x) * (prodQ n : ℝ)), e] at this
  linarith

/-- The support of `F` lies in 𝒜 ∩ (x, 2x], so its size is at most `N(x)`. -/
theorem support_le (x : ℝ) (hx : 6 ≤ x) :
    (((Nset x).filter (fun n => 0 < F x n)).card : ℝ) ≤ NN x := by
  have hx0 : 0 ≤ x := by linarith
  have hsub : (Nset x).filter (fun n => 0 < F x n) ⊆
      (Ioc ⌊x⌋₊ ⌊2 * x⌋₊).filter (fun n => Even n ∧ AtMostPrimes 2 n) := by
    intro n hn
    simp only [Finset.mem_filter, Nset] at hn ⊢
    refine ⟨hn.1, ?_⟩
    obtain ⟨p, hp, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := (P1 x).filter (fun p => p < n ∧ (n - p).Prime))
      (f := fun p => Real.log (p : ℝ)) (by unfold F at hn; exact hn.2.ne')
    simp only [P1, Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨hp3, hpx⟩, hpp⟩, hpn, hq⟩ := hp
    have hnx : x < n := (Nat.floor_lt hx0).mp (Finset.mem_Ioc.mp hn.1).1
    have hpxr : (p : ℝ) ≤ x - 3 := by
      have := Nat.floor_le (show (0 : ℝ) ≤ x - 3 by linarith)
      have h2 : (p : ℝ) ≤ ⌊x - 3⌋₊ := by exact_mod_cast hpx
      linarith
    have hq3 : 3 ≤ n - p := by
      have : (p : ℝ) + 3 < n := by linarith
      have : p + 3 < n := by exact_mod_cast this
      omega
    have h1 : Odd p := hpp.odd_of_ne_two (by omega)
    have h2 : Odd (n - p) := hq.odd_of_ne_two (by omega)
    have hsum : p + (n - p) = n := Nat.add_sub_cancel' hpn.le
    refine ⟨?_, ?_⟩
    · have := h1.add_odd h2; rwa [hsum] at this
    · have := (AtMostPrimes.prime hpp).add (AtMostPrimes.prime hq); rwa [hsum] at this
  have hc := Finset.card_le_card hsub
  have hsplit : NCount (2 * x) = NCount x +
      ((Ioc ⌊x⌋₊ ⌊2 * x⌋₊).filter (fun n => Even n ∧ AtMostPrimes 2 n)).card := by
    unfold NCount
    have hle : ⌊x⌋₊ ≤ ⌊2 * x⌋₊ := Nat.floor_le_floor (by linarith)
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      rw [← Finset.filter_union]
      congr 1
      ext n; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]; omega
    · apply Finset.disjoint_filter_filter
      rw [Finset.disjoint_left]; intro n h1 h2
      simp only [Finset.mem_Icc, Finset.mem_Ioc] at h1 h2; omega
  unfold NN A
  rw [hsplit]; push_cast
  have : (((Nset x).filter (fun n => 0 < F x n)).card : ℝ) ≤
      ((Ioc ⌊x⌋₊ ⌊2 * x⌋₊).filter (fun n => Even n ∧ AtMostPrimes 2 n)).card := by exact_mod_cast hc
  linarith

/-- **(5.5), PROVED from Lemma 8** in the `≤` form: for `x ≥ 10^52`,
`Ψ(x) ≤ (16CxN(x)/(1.6 + log x))^{11/15} G(x)^{4/15}`. -/
theorem eq55_of_lemma8 {C : ℝ} (hC0 : 0 ≤ C) (h8 : Lemma8 C) : Eq55 C G := by
  intro x hx
  have hx6 : 6 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  set c := 16 * C * x / (1.6 + Real.log x) with hc
  have hc0 : 0 ≤ c := by positivity
  rw [psi_eq x hx6]
  -- Hölder with the indicator of the support
  have hpq : (15 / 11 : ℝ).HolderConjugate (15 / 4) :=
    (Real.holderConjugate_iff_eq_conjExponent (by norm_num)).mpr (by norm_num)
  set s := Nset x
  set χ : ℕ → ℝ := fun n => if 0 < F x n then 1 else 0
  have hχF : ∑ n ∈ s, F x n = ∑ n ∈ s, χ n * F x n := by
    apply Finset.sum_congr rfl; intro n _
    simp only [χ]; split_ifs with h
    · ring
    · have := F_nonneg x n; have : F x n = 0 := by linarith
      rw [this]; ring
  have hH := Real.inner_le_Lp_mul_Lq_of_nonneg s hpq (f := χ) (g := F x)
    (fun n _ => by simp only [χ]; split_ifs <;> norm_num) (fun n _ => F_nonneg x n)
  have hχs : ∑ n ∈ s, χ n ^ (15 / 11 : ℝ) = ((s.filter (fun n => 0 < F x n)).card : ℝ) := by
    rw [Finset.card_filter]; push_cast
    apply Finset.sum_congr rfl; intro n _
    simp only [χ]; split_ifs <;> simp
  rw [hχs] at hH
  -- Σ F^{15/4} ≤ c^{11/4} G
  have hF4 : ∑ n ∈ s, F x n ^ (15 / 4 : ℝ) ≤ c ^ (11 / 4 : ℝ) * G x := by
    unfold G; rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro n hn
    have hF0 := F_nonneg x n
    have hFle := F_le hC0 h8 x hx n hn
    have hP := Pn_pos n
    have e : F x n ^ (15 / 4 : ℝ) = F x n * F x n ^ (11 / 4 : ℝ) := by
      rcases hF0.lt_or_eq with h | h
      · rw [show (15 / 4 : ℝ) = 1 + 11 / 4 by norm_num, rpow_add h, rpow_one]
      · rw [← h, zero_rpow (by norm_num), zero_mul]
    rw [e]
    have h1 : F x n ^ (11 / 4 : ℝ) ≤ (c * Pn n) ^ (11 / 4 : ℝ) :=
      rpow_le_rpow hF0 hFle (by norm_num)
    rw [mul_rpow hc0 hP.le] at h1
    have := mul_le_mul_of_nonneg_left h1 hF0
    linarith [show F x n * (c ^ (11 / 4 : ℝ) * Pn n ^ (11 / 4 : ℝ)) =
      c ^ (11 / 4 : ℝ) * (F x n * Pn n ^ (11 / 4 : ℝ)) by ring]
  have hG0 : 0 ≤ G x := by
    unfold G; apply Finset.sum_nonneg; intro n _
    exact mul_nonneg (F_nonneg x n) (rpow_nonneg (Pn_pos n).le _)
  have hN := support_le x hx6
  have hcard0 : (0 : ℝ) ≤ ((s.filter (fun n => 0 < F x n)).card : ℝ) := Nat.cast_nonneg _
  have hsum0 : 0 ≤ ∑ n ∈ s, F x n ^ (15 / 4 : ℝ) :=
    Finset.sum_nonneg fun n _ => rpow_nonneg (F_nonneg x n) _
  have h1 : ((s.filter (fun n => 0 < F x n)).card : ℝ) ^ (1 / (15 / 11) : ℝ) ≤ NN x ^ (11 / 15 : ℝ) := by
    rw [show (1 / (15 / 11) : ℝ) = 11 / 15 by norm_num]
    exact rpow_le_rpow hcard0 hN (by norm_num)
  have h2 : (∑ n ∈ s, F x n ^ (15 / 4 : ℝ)) ^ (1 / (15 / 4) : ℝ) ≤
      (c ^ (11 / 4 : ℝ) * G x) ^ (4 / 15 : ℝ) := by
    rw [show (1 / (15 / 4) : ℝ) = 4 / 15 by norm_num]
    exact rpow_le_rpow hsum0 hF4 (by norm_num)
  have hNN0 : 0 ≤ NN x := hcard0.trans hN
  have e2 : (c ^ (11 / 4 : ℝ) * G x) ^ (4 / 15 : ℝ) = c ^ (11 / 15 : ℝ) * G x ^ (4 / 15 : ℝ) := by
    rw [mul_rpow (by positivity) hG0, ← rpow_mul hc0]; norm_num
  have e3 : (16 * C * x * NN x / (1.6 + Real.log x)) ^ (11 / 15 : ℝ) =
      NN x ^ (11 / 15 : ℝ) * c ^ (11 / 15 : ℝ) := by
    rw [← mul_rpow hNN0 hc0, hc]; congr 1; ring
  rw [hχF, e3]
  calc ∑ n ∈ s, χ n * F x n
      ≤ ((s.filter (fun n => 0 < F x n)).card : ℝ) ^ (1 / (15 / 11) : ℝ) *
        (∑ n ∈ s, F x n ^ (15 / 4 : ℝ)) ^ (1 / (15 / 4) : ℝ) := hH
    _ ≤ NN x ^ (11 / 15 : ℝ) * ((c ^ (11 / 4 : ℝ) * G x) ^ (4 / 15 : ℝ)) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = NN x ^ (11 / 15 : ℝ) * c ^ (11 / 15 : ℝ) * G x ^ (4 / 15 : ℝ) := by rw [e2]; ring

/-- **The Theorem**, CONDITIONAL ON (2.14), Lemma 8 at the paper's C, Lemma 11, and the p. 105
bound for the concrete `G`, with `C₁ ≤ 6.2130`. -/
theorem statement27_of_L8_L11 {C₁ : ℝ} (hC10 : 1 < 2 * C₁ - 1) (hC1 : C₁ ≤ 6.2130)
    (hRS : RS33) (h8 : Lemma8 LeanLab.ChenExplicit.twinC) (h11 : Lemma11) (h510 : Eq510 C₁ G) :
    Statement27 :=
  statement27_of_sec5 hC10 hC1 hRS h8 h11
    (eq55_of_lemma8 (by linarith [LeanLab.ChenExplicit.twinC_bounds.1]) h8) h510

end LeanLab.SchnirelmannBounds.Vaughan1977Eq55

#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Eq55.Pn_pos
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Eq55.F_nonneg
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Eq55.psi_eq
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Eq55.F_le
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Eq55.support_le
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Eq55.eq55_of_lemma8
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Eq55.statement27_of_L8_L11

namespace LeanLab.SchnirelmannBounds.Vaughan1977Eq55
open LeanLab.SchnirelmannConstant LeanLab.RieselVaughan1983 LeanLab.SchnirelmannBounds.Vaughan1977
  LeanLab.SchnirelmannBounds.Vaughan1977Sec6 LeanLab.SchnirelmannBounds.Vaughan1977Lemma10
  LeanLab.SchnirelmannBounds.Vaughan1977Lemma12

/-- (5.10) as the bound for `G(x) - Ψ(x)`, which by (5.6) is `Σ_{1<d≤x} f(d) Σ_{d|n} F(n)`, the d = 1
term of (5.6) being `Σ_n F(n) = Ψ(x)`; (5.6) itself is not formalized here. -/
def Eq510tail (C₁ : ℝ) : Prop := ∀ x : ℝ, 10 ^ 52 ≤ x →
  G x - Psi x < x ^ 2 / Real.log x * (2 * C₁ - 2 + 47 / Real.log x)

/-- p. 105, "Hence, by (2.11), (5.10) and Lemma 11": the bound `Eq510` from Lemma 11 and (5.10),
for `C₁ ≥ 6.2022`, the lower half of (2.11). -/
theorem eq510_of (C₁ : ℝ) (hC1 : 6.2022 ≤ C₁) (h11 : Lemma11) (h510 : Eq510tail C₁) :
    Eq510 C₁ G := by
  intro x hx
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  refine ⟨?_, ?_⟩
  · unfold G; apply Finset.sum_nonneg; intro n _
    exact mul_nonneg (F_nonneg x n) (rpow_nonneg (Pn_pos n).le _)
  have h1 := (abs_lt.mp (h11 x hx)).2
  have h2 := h510 x hx
  have hl2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  -- Ψ < x²/L (1 + 0.4137/L)
  have hpsi : Psi x < x ^ 2 / Real.log x * (1 + 0.4138 / Real.log x) := by
    have e : x ^ 2 / Real.log x * (1 + (3 - 4 * Real.log 2) / (2 * Real.log x)) + 0.3 * x ^ 2 / Real.log x ^ 2
        = x ^ 2 / Real.log x * (1 + (1.8 - 2 * Real.log 2) / Real.log x) := by
      field_simp; ring
    have : x ^ 2 / Real.log x * (1 + (1.8 - 2 * Real.log 2) / Real.log x) ≤
        x ^ 2 / Real.log x * (1 + 0.4138 / Real.log x) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have : (1.8 - 2 * Real.log 2) / Real.log x ≤ 0.4138 / Real.log x :=
        div_le_div_of_nonneg_right (by linarith) hL.le
      linarith
    linarith
  have hsum : G x < x ^ 2 / Real.log x * (2 * C₁ - 1 + 47.4138 / Real.log x) := by
    have e : x ^ 2 / Real.log x * (1 + 0.4138 / Real.log x) +
        x ^ 2 / Real.log x * (2 * C₁ - 2 + 47 / Real.log x) =
        x ^ 2 / Real.log x * (2 * C₁ - 1 + 47.4138 / Real.log x) := by ring
    linarith
  have hfin : x ^ 2 / Real.log x * (2 * C₁ - 1 + 47.4138 / Real.log x) ≤
      (2 * C₁ - 1) / Real.log x * x ^ 2 * (1 + 4.2 / Real.log x) := by
    have e : (2 * C₁ - 1) / Real.log x * x ^ 2 * (1 + 4.2 / Real.log x) =
        x ^ 2 / Real.log x * (2 * C₁ - 1 + (2 * C₁ - 1) * 4.2 / Real.log x) := by ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : 47.4138 / Real.log x ≤ (2 * C₁ - 1) * 4.2 / Real.log x :=
      div_le_div_of_nonneg_right (by nlinarith) hL.le
    linarith
  linarith

/-- **The Theorem**, CONDITIONAL ON (2.14), Lemma 8 at the paper's C, Lemma 11 and (5.10), with
`6.2022 ≤ C₁ ≤ 6.2130` as in (2.11). -/
theorem statement27_of_L8_L11_510 {C₁ : ℝ} (hC1l : 6.2022 ≤ C₁) (hC1 : C₁ ≤ 6.2130)
    (hRS : RS33) (h8 : Lemma8 LeanLab.ChenExplicit.twinC) (h11 : Lemma11) (h510 : Eq510tail C₁) :
    Statement27 :=
  statement27_of_L8_L11 (by linarith) hC1 hRS h8 h11 (eq510_of C₁ hC1l h11 h510)

end LeanLab.SchnirelmannBounds.Vaughan1977Eq55

#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Eq55.eq510_of
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Eq55.statement27_of_L8_L11_510
