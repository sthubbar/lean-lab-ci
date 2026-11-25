import LeanLab.ExceptionalSet.SPLIT_feed1122_leaf_even_index_coefficient_domination
import LeanLab.ExceptionalSet.Feed1122DivisorEnvelopeTools

/-!
Split of `leaf_even_divisor_error_vanishes` of
`LeanLab.ExceptionalSet.SPLIT_feed1122_leaf_even_index_coefficient_domination`, burst-20261122
feed1122, session S89. Source P0082, Brudern and Perelli 1998, page 359 displays 14 and 15.

`divisorError r P m` is the sum of two envelopes: the truncated sum of display 14,
`(r/P) ∑_{q ≤ P, r ∣ q} q / (φ(q) φ(q/(m,q)))`, and the tail of display 15,
`r ∑_{q > P, r ∣ q} 1 / (φ(q) φ(q/(m,q)))`. Each leaf asks that one envelope be at most `η/2`
for large `N`, uniformly over `X/2 < m ≤ X` coprime to `r` and `1 ≤ r ≤ P = X^{6δ}`; the
assembly unfolds the definition and adds. Each leaf names one display only.

Why each is true: writing `q = r k`, with `(m, r) = 1`, one has `q/(m,q) = r k/(m,k)` and
`φ(q/(m,q)) ≥ φ(r) φ(k/(m,k))`. Grouping `k` by `(m,k)` gives each envelope at most
`τ(m) log P / P` times a power of `log log P`, and the divisor bound gives `τ(m) = X^{o(1)}`
against `P = X^{6δ}`. Neither bound needs the conductor to be large.

Session S134, burst-20261122: both leaves PROVED, with no new sorry, from the PROVED tools in
`LeanLab.ExceptionalSet.Feed1122DivisorEnvelopeTools`: `n/φ(n) ≤ A n^{1/8}`, the grouping of `q`
by `(M, q)`, the harmonic bound and an integral comparison for `∑ j^{-7/4}`, with the lab's PROVED
divisor bound `HeathBrown1985.card_divisors_le_rpow`. The truncated envelope is at most
`9 A² C / P^{1/2}` and the tail at most `3 A² C / P^{5/8}`.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp559b

open Real Finset Filter Topology
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)

/-! Glue for the two envelopes, session S134: the size facts for `P = X^{6δ}` with
`X = F γ N`, and the final arithmetic in `s = P^{1/8}`. -/

/-- Powers of `P ≥ 1` in terms of `s = P^{1/8}`. -/
theorem envelope_rpow_facts (P : ℝ) (hP : 1 ≤ P) :
    1 ≤ P ^ ((1 : ℝ) / 8) ∧ P ^ ((1 : ℝ) / 4) = (P ^ ((1 : ℝ) / 8)) ^ 2 ∧
      P = (P ^ ((1 : ℝ) / 8)) ^ 8 ∧ 1 + Real.log P ≤ 9 * P ^ ((1 : ℝ) / 8) ∧
      P ^ (-(3 : ℝ) / 4) = 1 / (P ^ ((1 : ℝ) / 8)) ^ 6 := by
  have hP0 : (0 : ℝ) < P := by linarith
  have hs1 : 1 ≤ P ^ ((1 : ℝ) / 8) := Real.one_le_rpow hP (by norm_num)
  refine ⟨hs1, ?_, ?_, ?_, ?_⟩
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hP0.le]
    norm_num
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hP0.le]
    norm_num
  · have h := Real.log_le_rpow_div hP0.le (show (0 : ℝ) < 1 / 8 by norm_num)
    have e : P ^ ((1 : ℝ) / 8) / (1 / 8) = 8 * P ^ ((1 : ℝ) / 8) := by ring
    linarith
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hP0.le, one_div ((P ^ _)), ← Real.rpow_neg hP0.le]
    norm_num

/-- Final arithmetic of display 14. -/
theorem envelope_arith_truncated (A C η s τ lg : ℝ) (_hA : 0 ≤ A) (hC : 0 ≤ C) (hη : 0 < η)
    (hs : 1 ≤ s) (hsL : 18 * A ^ 2 * C / η ≤ s) (_hτ0 : 0 ≤ τ) (hτ : τ ≤ C * s)
    (hlg0 : 0 ≤ lg) (hlg : lg ≤ 9 * s) :
    A ^ 2 * s ^ 2 * τ * lg / s ^ 8 ≤ η / 2 := by
  have hs0 : 0 < s := by linarith
  rw [div_le_iff₀ (by positivity)]
  have h2 : 18 * A ^ 2 * C ≤ η * s := by
    rw [div_le_iff₀ hη] at hsL
    linarith
  calc A ^ 2 * s ^ 2 * τ * lg ≤ A ^ 2 * s ^ 2 * (C * s) * (9 * s) := by gcongr
    _ = (18 * A ^ 2 * C) * s ^ 4 / 2 := by ring
    _ ≤ (η * s) * s ^ 4 / 2 := by gcongr
    _ = η / 2 * s ^ 5 := by ring
    _ ≤ η / 2 * s ^ 8 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hs (by norm_num)) (by positivity)

/-- Final arithmetic of display 15. -/
theorem envelope_arith_tail (A C η s τ : ℝ) (_hA : 0 ≤ A) (_hC : 0 ≤ C) (hη : 0 < η)
    (hs : 1 ≤ s) (hsL : 18 * A ^ 2 * C / η ≤ s) (_hτ0 : 0 ≤ τ) (hτ : τ ≤ C * s) :
    3 * A ^ 2 * τ * (1 / s ^ 6) ≤ η / 2 := by
  have hs0 : 0 < s := by linarith
  have h2 : 18 * A ^ 2 * C ≤ η * s := by
    rw [div_le_iff₀ hη] at hsL
    linarith
  rw [mul_one_div, div_le_iff₀ (by positivity)]
  calc 3 * A ^ 2 * τ ≤ 3 * A ^ 2 * (C * s) := by gcongr
    _ = (18 * A ^ 2 * C) * s / 6 := by ring
    _ ≤ (η * s) * s / 6 := by gcongr
    _ = η / 2 * (s ^ 2 / 3) := by ring
    _ ≤ η / 2 * s ^ 6 := by
        gcongr
        have : s ^ 2 ≤ s ^ 6 := pow_le_pow_right₀ hs (by norm_num)
        have : 0 ≤ s ^ 2 := by positivity
        linarith

/-- Size facts for `X = F γ N` and `P = X^{6δ}`: an `n/φ(n)` bound, and for large `N`,
`P ≥ 1`, `P^{1/8} ≥ L`, and `τ(M) ≤ C P^{1/8}` for `1 ≤ M ≤ X`. -/
theorem envelope_setup (γ : ℝ) (h1 : 1 < γ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1 / 100) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 ≤ C ∧
      (∀ n : ℕ, 1 ≤ n → (n : ℝ) / n.totient ≤ A * (n : ℝ) ^ ((1 : ℝ) / 8)) ∧
      ∀ L : ℝ, ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
        0 < F γ N ∧ 1 ≤ F γ N ^ (6 * δ) ∧ L ≤ (F γ N ^ (6 * δ)) ^ ((1 : ℝ) / 8) ∧
        ∀ M : ℕ, 1 ≤ M → (M : ℝ) ≤ F γ N →
          (M.divisors.card : ℝ) ≤ C * (F γ N ^ (6 * δ)) ^ ((1 : ℝ) / 8) := by
  set k : ℕ := ⌈8 / (6 * δ)⌉₊ + 8 with hkdef
  have hk1 : 1 ≤ k := by omega
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have hkδ : (k : ℝ)⁻¹ ≤ 6 * δ / 8 := by
    rw [inv_le_comm₀ hkpos (by positivity), inv_div]
    calc 8 / (6 * δ) ≤ (⌈8 / (6 * δ)⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ k := by rw [hkdef]; push_cast; linarith
  have hk8 : (k : ℝ)⁻¹ ≤ 1 / 8 := le_trans hkδ (by linarith)
  obtain ⟨A, hA, hAb⟩ :=
    LeanLab.ExceptionalSet.Feed1122DivisorEnvelope.div_totient_le_rpow k hk1
  obtain ⟨C, hC, hCb⟩ := LeanLab.HeathBrown1985.card_divisors_le_rpow k hk1
  refine ⟨A, C, hA.le, hC.le, fun n hn => ?_, fun L => ?_⟩
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact le_trans (hAb n hn)
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 hk8) hA.le)
  · have hX : Tendsto (fun N : ℕ => F γ (N : ℝ)) atTop atTop := by
      unfold LeanLab.ExceptionalSet.BrudernPerelli1998.F
      exact Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by linarith)).comp
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
    have hP : Tendsto (fun N : ℕ => (F γ (N : ℝ) ^ (6 * δ)) ^ ((1 : ℝ) / 8)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num)).comp ((tendsto_rpow_atTop (by linarith)).comp hX)
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.1
      ((hX.eventually_ge_atTop 1).and (hP.eventually_ge_atTop L))
    refine ⟨N₁, fun N hN => ?_⟩
    obtain ⟨hX1, hL⟩ := hN₁ N hN
    have hX0 : 0 < F γ N := by unfold LeanLab.ExceptionalSet.BrudernPerelli1998.F; exact Real.exp_pos _
    refine ⟨hX0, Real.one_le_rpow hX1 (by linarith), hL, fun M hM hMX => ?_⟩
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    calc (M.divisors.card : ℝ) ≤ C * (M : ℝ) ^ ((k : ℝ)⁻¹) := hCb M hM
      _ ≤ C * F γ N ^ ((k : ℝ)⁻¹) := by
          gcongr
      _ ≤ C * F γ N ^ (6 * δ * (1 / 8)) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)) hC.le
      _ = C * (F γ N ^ (6 * δ)) ^ ((1 : ℝ) / 8) := by
          rw [Real.rpow_mul hX0.le]

/-- LEAF: P0082 page 359 display 14, the truncated envelope of `Γ₁`, is `o(1)`: at most `η/2`
for large `N`, uniformly over `X/2 < m ≤ X` coprime to `r` and `1 ≤ r ≤ P = X^{6δ}`. HARD: the
grouping of `q = r k` by `(m, k)` and the divisor bound `τ(m) = X^{o(1)}`. -/
theorem leaf_divisor_envelope_truncated (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∀ η : ℝ, 0 < η → ∀ δ : ℝ, 0 < δ → δ < 1 / 100 →
      ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
        ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
          ∀ m : ℤ, F γ N / 2 < (m : ℝ) → (m : ℝ) ≤ F γ N → Int.gcd m r = 1 →
            (r : ℝ) / F γ N ^ (6 * δ) *
              ∑ q ∈ (Icc 1 ⌊F γ N ^ (6 * δ)⌋₊).filter (fun q => r ∣ q),
                (q : ℝ) / ((q.totient : ℝ) * ((q / Int.gcd m q).totient : ℝ)) ≤ η / 2 := by
  intro η hη δ hδ hδ1
  obtain ⟨A, C, hA, hC, hB, hev⟩ := envelope_setup γ h1 δ hδ hδ1
  obtain ⟨N₁, hN⟩ := hev (18 * A ^ 2 * C / η)
  refine ⟨N₁, fun N hN1 r hr _ m hm1 hm2 hg => ?_⟩
  obtain ⟨hX0, hP1, hPL, hτ⟩ := hN N hN1
  have hm0 : (0 : ℝ) < m := lt_trans (by positivity) hm1
  have hmZ : 0 < m := by exact_mod_cast hm0
  have hnat : ((m.natAbs : ℕ) : ℤ) = m := Int.natAbs_of_nonneg hmZ.le
  have hMm : ((m.natAbs : ℕ) : ℝ) = (m : ℝ) := by rw [← Int.cast_natCast, hnat]
  have hM1 : 1 ≤ m.natAbs := Int.natAbs_pos.2 hmZ.ne'
  have hcop : Nat.Coprime m.natAbs r := hg
  have hgq : ∀ q : ℕ, Int.gcd m (q : ℤ) = Nat.gcd m.natAbs q := fun q => rfl
  simp only [hgq]
  have hτM := hτ m.natAbs hM1 (by rw [hMm]; exact hm2)
  obtain ⟨hs1, hs2, hs8, hlog, hs6⟩ := envelope_rpow_facts _ hP1
  have hτ0 : (0 : ℝ) ≤ (m.natAbs.divisors.card : ℝ) := Nat.cast_nonneg _
  refine le_trans (LeanLab.ExceptionalSet.Feed1122DivisorEnvelope.truncated_bound A _ hA hP1
    r m.natAbs hr hM1 hcop hB) ?_
  have hlg0 : 0 ≤ 1 + Real.log (F γ N ^ (6 * δ)) := by linarith [Real.log_nonneg hP1]
  have key := envelope_arith_truncated A C η _ _ _ hA hC hη hs1 hPL hτ0 hτM hlg0 hlog
  rw [hs2]
  rw [← hs8] at key
  exact key

/-- LEAF: P0082 page 359 display 15, the tail envelope of `Γ₂`, is `o(1)`: at most `η/2` for
large `N`, uniformly over `X/2 < m ≤ X` coprime to `r` and `1 ≤ r ≤ P = X^{6δ}`. HARD: the
same grouping, with the tail of `∑ 1/φ(l)^2` and the divisor bound. -/
theorem leaf_divisor_envelope_tail (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∀ η : ℝ, 0 < η → ∀ δ : ℝ, 0 < δ → δ < 1 / 100 →
      ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
        ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
          ∀ m : ℤ, F γ N / 2 < (m : ℝ) → (m : ℝ) ≤ F γ N → Int.gcd m r = 1 →
            (r : ℝ) * ∑' q : ℕ, (if F γ N ^ (6 * δ) < (q : ℝ) ∧ r ∣ q then
              1 / ((q.totient : ℝ) * ((q / Int.gcd m q).totient : ℝ)) else 0) ≤ η / 2 := by
  intro η hη δ hδ hδ1
  obtain ⟨A, C, hA, hC, hB, hev⟩ := envelope_setup γ h1 δ hδ hδ1
  obtain ⟨N₁, hN⟩ := hev (18 * A ^ 2 * C / η)
  refine ⟨N₁, fun N hN1 r hr _ m hm1 hm2 hg => ?_⟩
  obtain ⟨hX0, hP1, hPL, hτ⟩ := hN N hN1
  have hm0 : (0 : ℝ) < m := lt_trans (by positivity) hm1
  have hmZ : 0 < m := by exact_mod_cast hm0
  have hnat : ((m.natAbs : ℕ) : ℤ) = m := Int.natAbs_of_nonneg hmZ.le
  have hMm : ((m.natAbs : ℕ) : ℝ) = (m : ℝ) := by rw [← Int.cast_natCast, hnat]
  have hM1 : 1 ≤ m.natAbs := Int.natAbs_pos.2 hmZ.ne'
  have hcop : Nat.Coprime m.natAbs r := hg
  have hgq : ∀ q : ℕ, Int.gcd m (q : ℤ) = Nat.gcd m.natAbs q := fun q => rfl
  simp only [hgq]
  have hτM := hτ m.natAbs hM1 (by rw [hMm]; exact hm2)
  obtain ⟨hs1, hs2, hs8, hlog, hs6⟩ := envelope_rpow_facts _ hP1
  have hτ0 : (0 : ℝ) ≤ (m.natAbs.divisors.card : ℝ) := Nat.cast_nonneg _
  refine le_trans (LeanLab.ExceptionalSet.Feed1122DivisorEnvelope.tail_bound A _ hA
    (by linarith) r m.natAbs hr hM1 hcop hB) ?_
  rw [hs6]
  exact envelope_arith_tail A C η _ _ hA hC hη hs1 hPL hτ0 hτM

/-- Assembly of `leaf_even_divisor_error_vanishes`: the two envelopes, each at most `η/2`. -/
theorem leaf_even_divisor_error_vanishes_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∀ η : ℝ, 0 < η → ∀ δ : ℝ, 0 < δ → δ < 1 / 100 →
      ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
        ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
          ∀ m : ℤ, F γ N / 2 < (m : ℝ) → (m : ℝ) ≤ F γ N → Int.gcd m r = 1 →
            divisorError r (F γ N ^ (6 * δ)) m ≤ η := by
  intro η hη δ hδ hδ1
  obtain ⟨Na, ha⟩ := leaf_divisor_envelope_truncated γ h1 h2 η hη δ hδ hδ1
  obtain ⟨Nb, hb⟩ := leaf_divisor_envelope_tail γ h1 h2 η hη δ hδ hδ1
  refine ⟨max Na Nb, fun N hN r hr hrP m hm1 hm2 hg => ?_⟩
  obtain ⟨hNa, hNb⟩ := max_le_iff.mp hN
  have hA := ha N hNa r hr hrP m hm1 hm2 hg
  have hB := hb N hNb r hr hrP m hm1 hm2 hg
  unfold divisorError
  linarith

end LeanLab.ExceptionalSet.UpJ200.Decomp559b
