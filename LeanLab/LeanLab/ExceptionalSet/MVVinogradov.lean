/-
Vinogradov's minor arc input reduced to Vinogradov's theorem itself, unit U-1032, PC run
20261019T0503Z-10740, T2, P0003 Vinogradov 1937 and P0091 Estermann 1938. AI wrote this Lean code.

`VinogradovDFT` is Vaughan, The Hardy-Littlewood Method, Theorem 3.1, for the data of
MVEstermann.lean: if `|k/M - a/q| ≤ q⁻²` with `a/q` in lowest terms, then
`|S(k/M)| ≤ C (x q^{-1/2} + x^{4/5} + (x q)^{1/2}) (log x)^4`. Theorem 3.1 is stated for
`Σ Λ(n) e(αn)`; the prime powers change the sum by `O(x^{1/2} log x)`, and
`𝓕 Φ k = S(-k/M)` has the modulus of `S(k/M)`, so the form below is the theorem. It is CITED.
`vinogradovMinor_of_dft` derives `VinogradovMinor` from it, through Dirichlet's approximation
theorem, `exists_rat_abs_sub_le_and_den_le`: a minor arc point has a rational approximation with
denominator in `(Q, M/Q]`. So Estermann 1938 rests on Theorem 3.1 and `MajorArcCount`.
KNOWN mathematics. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.MVEstermann

open ZMod Finset Real Filter Asymptotics

namespace LeanLab.ExceptionalSet.MV

attribute [local instance] Classical.propDecidable

/-- CITED. Vaughan, Theorem 3.1, in the form used here. -/
def VinogradovDFT : Prop :=
  ∃ (C : ℝ) (X0 : ℕ), ∀ x : ℕ, X0 ≤ x → ∀ (k : ZMod (Mx x)) (r : ℚ),
    |(ZMod.val k : ℝ) / (Mx x) - r| ≤ 1 / (r.den : ℝ) ^ 2 →
    ‖𝓕 (logPrimes x) k‖ ≤ C * ((x : ℝ) / √(r.den : ℝ) + (x : ℝ) ^ (4 / 5 : ℝ) +
      √((x : ℝ) * r.den)) * Real.log x ^ 4

/-- `(log x)^r ≤ x^s` for all large natural `x` -/
theorem log_rpow_le_rpow_nat (r : ℝ) {s : ℝ} (hs : 0 < s) :
    ∃ X : ℕ, ∀ x : ℕ, X ≤ x → Real.log x ^ r ≤ (x : ℝ) ^ s := by
  have h := (isLittleO_log_rpow_rpow_atTop r hs).bound one_pos
  obtain ⟨a, ha⟩ := eventually_atTop.mp h
  refine ⟨⌈max a 1⌉₊, fun x hx => ?_⟩
  have hxa : max a 1 ≤ (x : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hx)
  have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_right _ _) hxa
  have := ha x (le_trans (le_max_left _ _) hxa)
  rw [one_mul] at this
  have e2 : ‖(x : ℝ) ^ s‖ = (x : ℝ) ^ s := Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)
  rw [e2] at this
  exact le_trans (Real.le_norm_self _) this

/-- **Vinogradov's minor arc bound from Theorem 3.1.** PROVED, an implication. -/
theorem vinogradovMinor_of_dft (hV : VinogradovDFT) : VinogradovMinor := by
  obtain ⟨C, X0, hC⟩ := hV
  intro A hA
  refine ⟨2 * A + 8, fun B hB => ?_⟩
  obtain ⟨X1, h1⟩ := log_rpow_le_rpow_nat (A + 4) (s := 1 / 5) (by norm_num)
  obtain ⟨X2, h2⟩ := log_rpow_le_rpow_nat B (s := 1) one_pos
  refine ⟨4 * |C|, max (max X0 X1) (max X2 3), fun x hx k hk => ?_⟩
  have hx0 : X0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx1 : X1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx2 : X2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx3 : 3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hxr : (3 : ℝ) ≤ x := by exact_mod_cast hx3
  have hxpos : (0 : ℝ) < x := by linarith
  set L := Real.log x with hLdef
  have hL1 : 1 ≤ L := by
    have : Real.exp 1 ≤ x := by have := Real.exp_one_lt_d9; linarith
    rw [hLdef, Real.le_log_iff_exp_le (by linarith)]; exact this
  have hLpos : 0 < L := by linarith
  have hBpos : 0 < B := by linarith
  set Q := L ^ B with hQdef
  have hQ1 : 1 ≤ Q := Real.one_le_rpow hL1 hBpos.le
  have hQpos : 0 < Q := by linarith
  have hQx : Q ≤ x := by have := h2 x hx2; rwa [Real.rpow_one] at this
  have hM : (Mx x : ℝ) = 2 * x + 1 := by unfold Mx; push_cast; ring
  have hMpos : (0 : ℝ) < Mx x := by rw [hM]; linarith
  set n := ⌊(Mx x : ℝ) / Q⌋₊ with hn
  have hMQ : 2 ≤ (Mx x : ℝ) / Q := by
    rw [le_div_iff₀ hQpos, hM]; linarith
  have hn1 : 1 ≤ n := by
    rw [hn]; exact Nat.le_floor (by norm_num; linarith)
  have hnle : (n : ℝ) ≤ (Mx x : ℝ) / Q := Nat.floor_le (by positivity)
  have hnlt : (Mx x : ℝ) / Q < n + 1 := Nat.lt_floor_add_one _
  set ξ : ℝ := (ZMod.val k : ℝ) / (Mx x) with hξ
  obtain ⟨r, hr1, hr2⟩ := exists_rat_abs_sub_le_and_den_le ξ (n := n) (by omega)
  have hden1 : (1 : ℝ) ≤ r.den := by exact_mod_cast r.den_pos
  have hdenn : (r.den : ℝ) ≤ n := by exact_mod_cast hr2
  -- the denominator exceeds Q, else k is on a major arc
  have hQden : Q < r.den := by
    by_contra hcon
    push Not at hcon
    apply (mem_compl.mp hk)
    simp only [majorArcs, mem_filter, mem_univ, true_and]
    refine ⟨r.den, r.den_pos, hcon, r.num, ?_⟩
    have hrcast : ((r.num : ℝ) / (r.den : ℝ)) = (r : ℝ) := by
      rw [Rat.cast_def]
    rw [hrcast]
    calc |ξ - r| ≤ 1 / ((n + 1) * r.den) := hr1
      _ ≤ 1 / ((n : ℝ) + 1) := by
          apply one_div_le_one_div_of_le (by positivity)
          nlinarith
      _ ≤ Q / (Mx x) := by
          rw [div_le_div_iff₀ (by positivity) hMpos, one_mul]
          rw [div_lt_iff₀ hQpos] at hnlt
          linarith
  -- Theorem 3.1 applies
  have happ : |ξ - r| ≤ 1 / (r.den : ℝ) ^ 2 := by
    refine le_trans hr1 (one_div_le_one_div_of_le (by positivity) ?_)
    nlinarith
  have hS := hC x hx0 k r happ
  -- bound the bracket
  have hsqQ : √Q = L ^ (B / 2) := by
    rw [Real.sqrt_eq_rpow, hQdef, ← Real.rpow_mul hLpos.le]; ring_nf
  have hsqQpos : 0 < √Q := Real.sqrt_pos.mpr hQpos
  have t1 : (x : ℝ) / √(r.den : ℝ) ≤ x / √Q := by
    apply div_le_div_of_nonneg_left hxpos.le hsqQpos
    exact Real.sqrt_le_sqrt hQden.le
  have t3 : √((x : ℝ) * r.den) ≤ 2 * x / √Q := by
    rw [le_div_iff₀ hsqQpos, ← Real.sqrt_mul (by positivity)]
    have : (x : ℝ) * r.den * Q ≤ (2 * x) ^ 2 := by
      have h' : (r.den : ℝ) * Q ≤ Mx x := by
        have := le_trans hdenn hnle
        rwa [le_div_iff₀ hQpos] at this
      rw [hM] at h'
      nlinarith
    calc √((x : ℝ) * r.den * Q) ≤ √((2 * x) ^ 2) := Real.sqrt_le_sqrt this
      _ = 2 * x := Real.sqrt_sq (by linarith)
  have hbr : (x : ℝ) / √(r.den : ℝ) + (x : ℝ) ^ (4 / 5 : ℝ) + √((x : ℝ) * r.den)
      ≤ 3 * x / √Q + (x : ℝ) ^ (4 / 5 : ℝ) := by
    have : 3 * (x : ℝ) / √Q = x / √Q + 2 * x / √Q := by ring
    linarith
  -- the two pieces against x / L^A
  have hL4 : L ^ 4 = L ^ (4 : ℝ) := by rw [← Real.rpow_natCast]; norm_num
  have hLA : 0 < L ^ A := Real.rpow_pos_of_pos hLpos A
  have p1 : 3 * x / √Q * L ^ 4 ≤ 3 * x / L ^ A := by
    rw [hsqQ, hL4, div_mul_eq_mul_div, div_le_div_iff₀ (Real.rpow_pos_of_pos hLpos _) hLA]
    have e : L ^ (4 : ℝ) * L ^ A = L ^ (4 + A) := (Real.rpow_add hLpos _ _).symm
    have hle : L ^ (4 + A) ≤ L ^ (B / 2) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    have h3x : (0 : ℝ) ≤ 3 * x := by linarith
    calc 3 * (x : ℝ) * L ^ (4 : ℝ) * L ^ A = 3 * x * L ^ (4 + A) := by rw [mul_assoc, e]
      _ ≤ 3 * x * L ^ (B / 2) := mul_le_mul_of_nonneg_left hle h3x
  have p2 : (x : ℝ) ^ (4 / 5 : ℝ) * L ^ 4 ≤ x / L ^ A := by
    rw [le_div_iff₀ hLA, hL4, mul_assoc, ← Real.rpow_add hLpos]
    have := h1 x hx1
    calc (x : ℝ) ^ (4 / 5 : ℝ) * L ^ (4 + A) ≤ (x : ℝ) ^ (4 / 5 : ℝ) * (x : ℝ) ^ (1 / 5 : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hxpos.le _)
          rwa [add_comm] at this
      _ = x := by rw [← Real.rpow_add hxpos]; norm_num
  -- assemble
  have hL4pos : 0 ≤ L ^ 4 := by positivity
  have hbr0 : 0 ≤ (x : ℝ) / √(r.den : ℝ) + (x : ℝ) ^ (4 / 5 : ℝ) + √((x : ℝ) * r.den) := by
    positivity
  calc ‖𝓕 (logPrimes x) k‖
      ≤ C * ((x : ℝ) / √(r.den : ℝ) + (x : ℝ) ^ (4 / 5 : ℝ) + √((x : ℝ) * r.den)) * L ^ 4 := hS
    _ ≤ |C| * ((x : ℝ) / √(r.den : ℝ) + (x : ℝ) ^ (4 / 5 : ℝ) + √((x : ℝ) * r.den)) * L ^ 4 := by
        gcongr; exact le_abs_self C
    _ ≤ |C| * (3 * x / √Q + (x : ℝ) ^ (4 / 5 : ℝ)) * L ^ 4 := by gcongr
    _ = |C| * (3 * x / √Q * L ^ 4 + (x : ℝ) ^ (4 / 5 : ℝ) * L ^ 4) := by ring
    _ ≤ |C| * (3 * x / L ^ A + x / L ^ A) := by gcongr
    _ = 4 * |C| * x / L ^ A := by ring

/-- **Estermann 1938, CONDITIONAL ON Vaughan's Theorem 3.1 and `MajorArcCount`.** -/
theorem estermann_of_vinogradov (hV : VinogradovDFT) (hMa : MajorArcCount) : LogPowerSaving :=
  estermann_of_cited (vinogradovMinor_of_dft hV) hMa

#print axioms log_rpow_le_rpow_nat
#print axioms vinogradovMinor_of_dft
#print axioms estermann_of_vinogradov

end LeanLab.ExceptionalSet.MV
