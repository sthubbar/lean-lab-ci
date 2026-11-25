/-
Split of `prop56`, burst-20261122 session S144.
Helfgott, The ternary Goldbach conjecture is true, arXiv 1312.7748v2, Proposition 5.6,
page 39 display (5.23). The proof writes `G_q(R) = φ(q)/q (log R + c_E + Σ_{p|q} log p/p) + err_{q,R}`,
display (5.24), and reduces (5.23) to display (5.26) on page 39, using
`ρ ≤ (log Q₀ + c₊)/(log Q + c_E) ≤ ω(ρ)` and `c₊ ≥ ρ c_E`. The rest of the proof,
pages 39 to 44, establishes (5.26).
The glue `prop56_of_leaves` is sorry free.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Feed1122Decomp580aP2

namespace LeanLab.Ternary.Task580

/-- LEAF: the numerical value of `c_E`, Helfgott 1312.7748v2 page 37 display (5.14),
`c_E = γ + Σ_p log p/(p(p-1)) = 1.3325822...`, used here only in the weak form `c_E ≤ 2`,
which is what `c₊ ≥ ρ c_E` on page 39 needs for `ρ ≤ 0.6`. Class MEDIUM. -/
theorem sieveConstant_le : sieveConstant ≤ 2 := by
  sorry

/-- LEAF: display (5.26), Helfgott 1312.7748v2 page 39, proved on pages 39 to 44 by
(5.27) to (5.31), Lemma 5.5 and an interval arithmetic computation over `q < 3.3·10⁹`.
Class HARD. Here `Q₀,min = 10⁵`, `ρ = log Q₀/log Q`,
`ω(ρ) = (log Q₀,min + c₊)/(ρ⁻¹ log Q₀,min + c_E)`, `c₊ = 1.36`, `c_Δ = c₊ - c_E`, and
`err_{q,R} = G_q(R) - φ(q)/q (log R + c_E + Σ_{p|q} log p/p)` as in (5.24). -/
theorem prop56_display526 (Q Q₀ : ℝ) (hQ₀ : 1e5 ≤ Q₀) (hQ : 20000 * Q₀ ≤ Q)
    (hρ : Real.log Q₀ ≤ 0.6 * Real.log Q) (q : ℕ) (hq : 1 ≤ q) (hqQ : (q : ℝ) ≤ Q₀)
    (s : ℝ) (hs1 : 1 ≤ s) (hs : s ≤ Q₀ / q) :
    (q : ℝ) / (Nat.totient q : ℝ) *
        (sieveG q (Q₀ / (s * q)) - (Nat.totient q : ℝ) / q *
          (Real.log (Q₀ / (s * q)) + sieveConstant +
            ∑ p ∈ q.primeFactors, Real.log p / p)) +
      (Real.log 1e5 + 1.36) /
          (Real.log 1e5 / (Real.log Q₀ / Real.log Q) + sieveConstant) *
        max 0 (-((q : ℝ) / (Nat.totient q : ℝ) *
          (sieveG q (Q / (s * q)) - (Nat.totient q : ℝ) / q *
            (Real.log (Q / (s * q)) + sieveConstant +
              ∑ p ∈ q.primeFactors, Real.log p / p)))) ≤
      (1 - (Real.log 1e5 + 1.36) /
          (Real.log 1e5 / (Real.log Q₀ / Real.log Q) + sieveConstant)) *
        (Real.log (s * q) - ∑ p ∈ q.primeFactors, Real.log p / p) +
      (1.36 - sieveConstant) := by
  sorry

/-- `c_E ≥ 0`, from (5.14): `γ > 1/2` and every summand is nonnegative. -/
theorem sieveConstant_nonneg : 0 ≤ sieveConstant := by
  unfold sieveConstant
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have : 0 ≤ ∑' p : ℕ, (if p.Prime then Real.log p / ((p : ℝ) * (p - 1 : ℝ)) else 0) := by
    apply tsum_nonneg
    intro p
    split_ifs with hp
    · have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      apply div_nonneg (Real.log_nonneg (by linarith))
      apply mul_nonneg (by linarith) (by linarith)
    · exact le_rfl
  linarith

/-- `G_q(R) ≥ 1` for `R ≥ 1`, from the term `r = 1` of (5.5). -/
theorem one_le_sieveG (q : ℕ) (R : ℝ) (hR : 1 ≤ R) : 1 ≤ sieveG q R := by
  unfold sieveG
  have hmem : 1 ∈ (Finset.Icc 1 ⌊R⌋₊).filter (fun r => Nat.Coprime r q) := by
    simp only [Finset.mem_filter, Finset.mem_Icc, le_refl, true_and, Nat.coprime_one_left_eq_true,
      and_true]
    exact Nat.one_le_floor_iff _ |>.mpr hR
  have h := Finset.single_le_sum (f := fun r : ℕ =>
      ((ArithmeticFunction.moebius r : ℝ)) ^ 2 / (Nat.totient r : ℝ))
    (fun r _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) hmem
  simpa using h

/-- `Σ_{p|q} log p/p ≤ log q`, used on page 39 for `log sq - Σ_{p|q} log p/p ≥ 0`. -/
theorem sum_log_primeFactors_le (q : ℕ) (hq : 1 ≤ q) :
    ∑ p ∈ q.primeFactors, Real.log p / p ≤ Real.log q := by
  have h1 : ∑ p ∈ q.primeFactors, Real.log p / p ≤ ∑ p ∈ q.primeFactors, Real.log p := by
    apply Finset.sum_le_sum
    intro p hp
    have hp2 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
    exact div_le_self (Real.log_nonneg hp2) hp2
  have h2 : ∑ p ∈ q.primeFactors, Real.log p = Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) := by
    rw [Real.log_prod]
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).pos
    positivity
  have h3 : (∏ p ∈ q.primeFactors, (p : ℝ)) ≤ q := by
    have hd := Nat.prod_primeFactors_dvd q
    have := Nat.le_of_dvd (by omega) hd
    rw [← Nat.cast_prod]
    exact_mod_cast this
  have h4 : 0 < (∏ p ∈ q.primeFactors, (p : ℝ)) := by
    apply Finset.prod_pos
    intro p hp
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  rw [h2] at h1
  exact h1.trans (Real.log_le_log h4 h3)

/-- `(log Q₀ + c₊)/(log Q + c_E) ≤ ω(ρ)` when `Q₀ ≥ Q₀,min` and `c₊ ≥ ρ c_E`,
Helfgott 1312.7748v2 page 39 below (5.25). -/
theorem omega_ge_aux (a b L cE : ℝ) (hL : 0 < L) (haL : L ≤ a) (hb : 0 < b)
    (hcE0 : 0 ≤ cE) (hcb : cE * a ≤ 1.36 * b) :
    (a + 1.36) / (b + cE) ≤ (L + 1.36) / (L / (a / b) + cE) := by
  have ha0 : 0 < a := by linarith
  have hω' : (L + 1.36) / (L / (a / b) + cE) = (L + 1.36) * a / (L * b + cE * a) := by
    rw [div_div_eq_mul_div, div_add' _ _ _ ha0.ne', div_div_eq_mul_div]
  rw [hω', div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.2 haL) (sub_nonneg.2 hcb)]

/-- Proposition 5.6, Helfgott 1312.7748v2 page 39 display (5.23).
This is the statement of `prop56`, copied verbatim.
CONDITIONAL ON `sieveConstant_le` and `prop56_display526`. -/
theorem prop56_of_leaves (Q Q₀ : ℝ) (hQ₀ : 1e5 ≤ Q₀) (hQ : 20000 * Q₀ ≤ Q)
    (hρ : Real.log Q₀ ≤ 0.6 * Real.log Q) (q : ℕ) (hq : 1 ≤ q) (hqQ : (q : ℝ) ≤ Q₀)
    (s : ℝ) (hs1 : 1 ≤ s) (hs : s ≤ Q₀ / q) :
    sieveG q (Q₀ / (s * q)) / sieveG q (Q / (s * q)) ≤
      (Real.log Q₀ + 1.36) / (Real.log Q + sieveConstant) := by
  have h526 := prop56_display526 Q Q₀ hQ₀ hQ hρ q hq hqQ s hs1 hs
  have hcE0 := sieveConstant_nonneg
  have hcE1 := sieveConstant_le
  have hQ₀pos : 0 < Q₀ := by norm_num at hQ₀; linarith
  have hQpos : 0 < Q := by linarith
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hspos : 0 < s := by linarith
  have hsqpos : 0 < s * q := mul_pos hspos hqpos
  have hsqle : s * q ≤ Q₀ := by rwa [le_div_iff₀ hqpos] at hs
  have hR1 : 1 ≤ Q / (s * q) := by
    rw [le_div_iff₀ hsqpos]; linarith
  have hB := one_le_sieveG q (Q / (s * q)) hR1
  have hL : 0 < Real.log 1e5 := Real.log_pos (by norm_num)
  have haL : Real.log 1e5 ≤ Real.log Q₀ := Real.log_le_log (by norm_num) hQ₀
  have hb : 0 < Real.log Q := by
    apply Real.log_pos; norm_num at hQ₀; linarith
  have hlR : Real.log (Q₀ / (s * q)) = Real.log Q₀ - Real.log (s * q) :=
    Real.log_div hQ₀pos.ne' hsqpos.ne'
  have hlR' : Real.log (Q / (s * q)) = Real.log Q - Real.log (s * q) :=
    Real.log_div hQpos.ne' hsqpos.ne'
  have hX : 0 ≤ Real.log (s * q) - ∑ p ∈ q.primeFactors, Real.log p / p := by
    rw [Real.log_mul hspos.ne' hqpos.ne']
    have := sum_log_primeFactors_le q hq
    have := Real.log_nonneg hs1
    linarith
  have hφ : (0 : ℝ) < (Nat.totient q : ℝ) := by exact_mod_cast Nat.totient_pos.2 (by omega)
  set cE := sieveConstant with hcE
  set a := Real.log Q₀ with ha
  set b := Real.log Q with hb'
  set L := Real.log 1e5 with hL'
  set l := Real.log (s * q) with hl
  set P := ∑ p ∈ q.primeFactors, Real.log p / p with hP
  set A := sieveG q (Q₀ / (s * q)) with hA
  set B := sieveG q (Q / (s * q)) with hB'
  set ω := (L + 1.36) / (L / (a / b) + cE) with hω
  set T := (a + 1.36) / (b + cE) with hT
  set k := (q : ℝ) / (Nat.totient q : ℝ) with hk
  have hk0 : 0 < k := div_pos hqpos hφ
  have hkφ : k * ((Nat.totient q : ℝ) / q) = 1 := by
    rw [hk]; field_simp
  set E1 := k * (A - (Nat.totient q : ℝ) / q * (Real.log (Q₀ / (s * q)) + cE + P)) with hE1
  set E2 := k * (B - (Nat.totient q : ℝ) / q * (Real.log (Q / (s * q)) + cE + P)) with hE2
  have hkA : k * A = a - l + cE + P + E1 := by
    rw [hE1, hlR, mul_sub, ← mul_assoc, hkφ]; ring
  have hkB : k * B = b - l + cE + P + E2 := by
    rw [hE2, hlR', mul_sub, ← mul_assoc, hkφ]; ring
  have hbc : 0 < b + cE := by linarith
  have hTeq : T * (b + cE) = a + 1.36 := by rw [hT]; field_simp
  have hT0 : 0 ≤ T := div_nonneg (by linarith) hbc.le
  have hcb : cE * a ≤ 1.36 * b := by
    have h1 := mul_le_mul_of_nonneg_right hcE1 (show 0 ≤ a by linarith)
    linarith
  have hTω : T ≤ ω := omega_ge_aux a b L cE hL haL hb hcE0 hcb
  clear_value E1 E2 ω T k A B P l L a b cE
  have key : E1 ≤ (1 - T) * (l - P) + (1.36 - cE) + T * E2 := by
    have h1 : (1 - ω) * (l - P) ≤ (1 - T) * (l - P) := by
      have := mul_nonneg (sub_nonneg.2 hTω) hX
      linarith
    have h2 : -(ω * max 0 (-E2)) ≤ T * E2 := by
      rcases le_total 0 E2 with h | h
      · rw [max_eq_left (by linarith)]
        have := mul_nonneg hT0 h
        linarith
      · rw [max_eq_right (by linarith)]
        have := mul_nonneg (sub_nonneg.2 hTω) (neg_nonneg.2 h)
        linarith
    linarith
  have hB0 : 0 < B := by linarith
  rw [div_le_iff₀ hB0]
  have : k * A ≤ k * (T * B) := by
    have e : k * (T * B) = T * (k * B) := by ring
    rw [e, hkA, hkB]
    linarith [key, hTeq]
  exact le_of_mul_le_mul_left this hk0

end LeanLab.Ternary.Task580
