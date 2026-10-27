/-
AI-written Lean code, Claude, 2026-10-21, session 20261021T0217Z-cloud56, unit U-6814, track T1.
P0002 J.-R. Chen 1973, Sci. Sinica 16, 157-176, p. 171, the step from (24) and (25) to (26),
read from the lab copy papers/P0002.pdf, page image rendered with pdftoppm.

By (24) the Selberg main term in `M_1` is `1/S`; (26) replaces it by `(8 + 24ε) C_x (log x)^{-1}`.
This file proves that replacement: for fixed `0 < ε < 1/6` and every large even `x`,
`S > 0` and `1/S ≤ (8 + 24ε) C_x / log x`, from `chen_display25_S`. The O(1) of (25) must be
beaten by the gap `(1/8 - ε/4) - 1/(8 + 24ε) = (ε - 6ε²)/(8 + 24ε)`, positive exactly for
`ε < 1/6`, against `C_x`, which is unbounded; this needs `C_x = o(log x)`, proved here from
`C_x ≤ x/(2φ(x))`, `x/φ(x) ≤ e(1 + ω(x))` and `ω(x)! ≤ x`.

The identity (24) is in Chen1973Display24 and the combined bound in Chen1973Selberg26; the rest of
Lemma 7, the sum over `p_1, p_2, n` with `Φ`, is not done.
Binary Goldbach is OPEN.
-/
import LeanLab.AlmostPrimeSums.Chen1973Display25
import LeanLab.HeathBrown1985.Elementary

open Finset Real

noncomputable section
namespace LeanLab.AlmostPrimeSums.Chen1973Display26

open LeanLab.AlmostPrimeSums.Chen1973V LeanLab.AlmostPrimeSums.Chen1973Display25

/-- A set of `k` naturals, each at least `2`, has product at least `(k + 1)!`. -/
lemma factorial_le_prod (s : Finset ℕ) (hs : ∀ p ∈ s, 2 ≤ p) :
    (s.card + 1).factorial ≤ ∏ p ∈ s, p := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have hs' : ∀ p ∈ s, 2 ≤ p := fun p hp => hs p (mem_insert_of_mem hp)
    have hna : a ∉ s := fun h => lt_irrefl a (ha a h)
    have hsub : s ⊆ Ico 2 a := fun p hp => mem_Ico.mpr ⟨hs' p hp, ha p hp⟩
    have hc : s.card + 2 ≤ a := by
      have ha2 : 2 ≤ a := hs a (mem_insert_self a s)
      have := card_le_card hsub; simp at this; omega
    rw [card_insert_of_notMem hna, prod_insert hna, Nat.factorial_succ]
    exact Nat.mul_le_mul (by omega) (ih hs')

/-- `ω(x)! ≤ x`. -/
lemma omega_factorial_le (x : ℕ) (hx : 1 ≤ x) : (x.primeFactors.card).factorial ≤ x :=
  (Nat.factorial_le (Nat.le_succ _)).trans ((factorial_le_prod _
    (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)).trans
    (Nat.le_of_dvd hx (Nat.prod_primeFactors_dvd x)))

/-- `ω(x) ≤ e^{1 + 1/δ} + δ log x` for every `δ > 0`, so `ω(x) = o(log x)`. -/
lemma omega_le_eps {δ : ℝ} (hδ : 0 < δ) (x : ℕ) (hx : 1 ≤ x) :
    (x.primeFactors.card : ℝ) ≤ exp (1 + 1 / δ) + δ * Real.log x := by
  set k := x.primeFactors.card
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hl := Real.log_natCast_nonneg x
  by_cases hk : (k : ℝ) < exp (1 + 1 / δ)
  · have := mul_nonneg hδ.le hl; linarith
  · push_neg at hk
    have hk0 : (0 : ℝ) < k := lt_of_lt_of_le (exp_pos _) hk
    have h1 := Real.pow_div_factorial_le_exp (x := (k : ℝ)) hk0.le k
    have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    have h2 : ((k.factorial : ℕ) : ℝ) ≤ x := by exact_mod_cast omega_factorial_le x hx
    rw [div_le_iff₀ hf] at h1
    have h3 : (k : ℝ) ^ k ≤ exp k * x :=
      h1.trans (mul_le_mul_of_nonneg_left h2 (exp_pos _).le)
    have h4 := Real.log_le_log (by positivity) h3
    rw [Real.log_pow, Real.log_mul (exp_pos _).ne' hx0.ne', Real.log_exp] at h4
    have h5 : 1 + 1 / δ ≤ Real.log k := by
      have := Real.log_le_log (exp_pos _) hk; rwa [Real.log_exp] at this
    have h6 : (k : ℝ) * (1 + 1 / δ) ≤ k + Real.log x := by nlinarith
    have h7 : (k : ℝ) / δ ≤ Real.log x := by
      have : (k : ℝ) * (1 + 1 / δ) = k + k / δ := by ring
      linarith
    rw [div_le_iff₀ hδ] at h7
    have := exp_pos (1 + 1 / δ)
    nlinarith

/-- `C_x ≤ x/(2φ(x))` for even `x`, from the Euler product of (25), whose sum is at least `1`. -/
lemma CN_le_div_totient {x : ℕ} (he : Even x) (hx : 0 < x) :
    LeanLab.ChenDoubleSieve.CN x ≤ (x : ℝ) / (2 * x.totient) := by
  have hm := totient_div_mul_tsum_a he hx.ne'
  have hA : 1 ≤ ∑' n, a x n := by
    have := (summable_a x).le_tsum 1 (fun j _ => a_nonneg x j)
    rwa [a_one] at this
  have hC : 0 < LeanLab.ChenDoubleSieve.CN x := by
    unfold LeanLab.ChenDoubleSieve.CN
    exact mul_pos (lt_of_lt_of_le one_pos (LeanLab.ChenExplicit.one_le_oddFactor x))
      LeanLab.ChenExplicit.twinC_pos
  have hφ : (0 : ℝ) < x.totient := by exact_mod_cast Nat.totient_pos.mpr hx
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have h1 : (x.totient : ℝ) / x ≤ 1 / (2 * LeanLab.ChenDoubleSieve.CN x) := by
    rw [← hm]
    exact le_mul_of_one_le_right (by positivity) hA
  rw [le_div_iff₀ (by positivity)]
  rw [div_le_div_iff₀ hx0 (by positivity)] at h1
  linarith

/-- `C_x ≤ 2 (1 + ω(x))` for even `x ≥ 2`. -/
lemma CN_le_omega {x : ℕ} (he : Even x) (hx : 0 < x) :
    LeanLab.ChenDoubleSieve.CN x ≤ 2 * (1 + x.primeFactors.card) := by
  have h1 := CN_le_div_totient he hx
  have h2 := LeanLab.HeathBrown1985.div_totient_le x hx
  have hφ : (0 : ℝ) < x.totient := by exact_mod_cast Nat.totient_pos.mpr hx
  have he3 := Real.exp_one_lt_d9
  have hω : (0 : ℝ) ≤ x.primeFactors.card := Nat.cast_nonneg _
  have e : (x : ℝ) / (2 * x.totient) = (x : ℝ) / x.totient / 2 := by ring
  rw [e] at h1
  nlinarith

/-- **Chen 1973, from (25) to (26), PROVED**: for fixed `0 < ε < 1/6` there is `x₀` with, for
every even `x ≥ x₀`, `S > 0` and `1/S ≤ (8 + 24ε) C_x / log x`, where
`S = ∑_{k ≤ z, (k,x)=1} μ²(k)/φ(k) ∏_{p∣k}(1 + 1/(p-2))`, `z = (x^{1/2-ε})^{1/2}`. -/
theorem chen26_inv_S {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 6) :
    ∃ x₀ : ℕ, ∀ x : ℕ, Even x → x₀ ≤ x →
      0 < S x (zC x ε) ∧
        1 / S x (zC x ε) ≤ (8 + 24 * ε) * LeanLab.ChenDoubleSieve.CN x / Real.log x := by
  obtain ⟨B, hB, hS⟩ := chen_display25_S
  obtain ⟨Δ, hΔd⟩ : ∃ Δ : ℝ, Δ = (1 / 8 - ε / 4) - 1 / (8 + 24 * ε) := ⟨_, rfl⟩
  have h824 : (0 : ℝ) < 8 + 24 * ε := by linarith
  have hΔ : 0 < Δ := by
    rw [hΔd, sub_pos, div_lt_iff₀ h824]; nlinarith
  obtain ⟨δ, hδd⟩ : ∃ δ : ℝ, δ = Δ / (4 * (B + 1)) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδd]; positivity
  set M := exp (1 + 1 / δ)
  have hM : 0 < M := exp_pos _
  set T := 4 * B * (1 + M) / Δ + 1
  refine ⟨⌈exp T⌉₊ + 1, fun x he hx => ?_⟩
  have hx1 : 1 ≤ x := by omega
  have hxpos : 0 < x := by omega
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hxpos
  have hTL : T ≤ Real.log x := by
    have h1 : exp T ≤ (x : ℝ) := by
      have := Nat.le_ceil (exp T)
      have h2 : ((⌈exp T⌉₊ : ℕ) : ℝ) ≤ x := by exact_mod_cast (by omega : ⌈exp T⌉₊ ≤ x)
      linarith
    have := Real.log_le_log (exp_pos _) h1
    rwa [Real.log_exp] at this
  set L := Real.log x
  have hT0 : 1 ≤ T := by
    have : 0 ≤ 4 * B * (1 + M) / Δ := by positivity
    linarith
  have hL0 : 0 < L := by linarith
  set c := LeanLab.ChenDoubleSieve.CN x
  have hc : 0 < c := by
    simp only [c]; unfold LeanLab.ChenDoubleSieve.CN
    exact mul_pos (lt_of_lt_of_le one_pos (LeanLab.ChenExplicit.one_le_oddFactor x))
      LeanLab.ChenExplicit.twinC_pos
  have hcω := CN_le_omega he hxpos
  have hω := omega_le_eps hδ x hx1
  have hc2 : c ≤ 2 * (1 + M + δ * L) := by
    have : c ≤ 2 * (1 + x.primeFactors.card) := hcω
    linarith
  have hBc : B * c ≤ Δ * L := by
    have e1 : B * c ≤ 2 * B * (1 + M) + 2 * B * δ * L := by nlinarith
    have e2 : 2 * B * δ ≤ Δ / 2 := by
      rw [hδd, show 2 * B * (Δ / (4 * (B + 1))) = Δ / 2 * (B / (B + 1)) by field_simp; ring]
      apply mul_le_of_le_one_right (by linarith)
      rw [div_le_one (by linarith)]; linarith
    have e3 : 2 * B * (1 + M) ≤ Δ / 2 * L := by
      have : 4 * B * (1 + M) / Δ ≤ L := by linarith
      rw [div_le_iff₀ hΔ] at this; linarith
    nlinarith [mul_le_mul_of_nonneg_right e2 hL0.le]
  have hmain := hS x he hxpos ε
  have hkey : L / ((8 + 24 * ε) * c) ≤ (1 / 8 - ε / 4) * L / c - B := by
    have e : (1 / 8 - ε / 4) * L / c - B - L / ((8 + 24 * ε) * c) = Δ * L / c - B := by
      rw [hΔd]; field_simp; ring
    have : B ≤ Δ * L / c := by rw [le_div_iff₀ hc]; linarith
    linarith
  have hpos : 0 < L / ((8 + 24 * ε) * c) := by positivity
  have hSL : L / ((8 + 24 * ε) * c) ≤ S x (zC x ε) := hkey.trans hmain
  refine ⟨hpos.trans_le hSL, ?_⟩
  have := one_div_le_one_div_of_le hpos hSL
  rw [one_div_div] at this
  rw [mul_div_assoc] at this ⊢
  linarith

/-- Vacuity check: `ε = 1/10` meets `0 < ε < 1/6`, so `chen26_inv_S` gives a genuine
threshold, and the constant is `8 + 24/10 = 10.4`. -/
theorem chen26_instance : ∃ x₀ : ℕ, ∀ x : ℕ, Even x → x₀ ≤ x →
    0 < S x (zC x (1 / 10)) ∧
      1 / S x (zC x (1 / 10)) ≤ 10.4 * LeanLab.ChenDoubleSieve.CN x / Real.log x := by
  obtain ⟨x₀, h⟩ := chen26_inv_S (ε := 1 / 10) (by norm_num) (by norm_num)
  refine ⟨x₀, fun x he hx => ?_⟩
  have := h x he hx
  norm_num at this ⊢
  exact this

end LeanLab.AlmostPrimeSums.Chen1973Display26
