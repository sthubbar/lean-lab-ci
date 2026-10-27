/-
AI-written Lean code, Claude, 2026-10-20, session 20261020T2217Z-cloud52, unit U-6752, track T1.
P0002 J.-R. Chen 1973, Sci. Sinica 16, 157-176, read from the lab copy papers/P0002.pdf,
page images. This file formalizes pieces of Chen's OWN text:
* Section I: Chen's count `P_x(1,2)`, the primes `p` with `x - p = p₁` or `x - p = p₂p₃`,
  and its exact relation to the lab's `D12` and `chenCount`; Theorem I in Chen's own form
  implies the lab's `Chen1973Quant`.
* Lemma 9, display (33): the integrand identity, the closed form of the `u`-integral,
  the elementary inequality `log x ≤ (x-1)/2 + (x-1)/(1+x)` Chen uses on `[1,2]`, and
  the numerical value of the closed form.
* Lemmas 8, 9 and Section III, display (34): the constant arithmetic
  `8 · 0.49254 ≤ 3.9404`, `8 · 0.3301 = 2.6408`, `2.6408 - 3.9404/2 ≥ 0.67`, and an
  assembly lemma.
QUESTION, not a finding: Chen prints the closed form in (33) as `≥ -0.0164725`; its value
is `1/2 + 3 log 3 - (11/2) log 2 ≈ -0.01647263`, so the printed lower bound is off by about
`1.3·10⁻⁷`; `chen33_value_bounds` proves the true value lies in `(-0.0164727, -0.0164725)`.
The slip does not affect Lemma 9: `lemma9_margin` proves `0.3301 ≤ log 4 - log 8/2 + v`
with the true value `v`.
Binary Goldbach is OPEN.
-/
import LeanLab.AlmostPrimeSums.Chen1973

open Finset Real
open scoped ArithmeticFunction.Omega

noncomputable section
namespace LeanLab.AlmostPrimeSums.Chen1973Own

open LeanLab.ChenDoubleSieve LeanLab.ChenExplicit

/-! ### 1. Chen's count `P_x(1,2)`, Section I -/

/-- Chen's representation predicate: `n = p₁` or `n = p₂ p₃`, with `p₁, p₂, p₃` primes,
not necessarily distinct. -/
def ChenRep (n : ℕ) : Prop := n.Prime ∨ ∃ a b : ℕ, a.Prime ∧ b.Prime ∧ n = a * b

/-- `P_x(1,2)`, Chen Section I: the number of primes `p` with `x - p = p₁` or `x - p = p₂p₃`.
Such `p` satisfy `p < x`, so the count runs over `range x`. -/
def chenP (x : ℕ) : ℕ := by
  classical exact #{p ∈ range x | p.Prime ∧ ChenRep (x - p)}

/-- **Chen's "product of at most two primes" in `Ω` form**: `n = p₁` or `n = p₂p₃` iff
`n ≠ 1`, `n ≠ 0` and `Ω n ≤ 2`, i.e. `1 ≤ Ω n ≤ 2` with multiplicity. -/
theorem chenRep_iff (n : ℕ) : ChenRep n ↔ Nat.IsAtMostAlmostPrime 2 n ∧ n ≠ 1 := by
  constructor
  · rintro (hp | ⟨a, b, ha, hb, rfl⟩)
    · exact ⟨⟨hp.ne_zero, by rw [ArithmeticFunction.cardFactors_apply_prime hp]; norm_num⟩,
        hp.one_lt.ne'⟩
    · refine ⟨⟨mul_ne_zero ha.ne_zero hb.ne_zero, ?_⟩, ?_⟩
      · rw [ArithmeticFunction.cardFactors_mul ha.ne_zero hb.ne_zero,
          ArithmeticFunction.cardFactors_apply_prime ha,
          ArithmeticFunction.cardFactors_apply_prime hb]
      · exact (Nat.one_lt_mul_iff.mpr ⟨ha.pos, hb.pos, Or.inl ha.one_lt⟩).ne'
  · rintro ⟨⟨h0, h2⟩, h1⟩
    have hpos : Ω n ≠ 0 := by
      rw [Ne, ArithmeticFunction.cardFactors_eq_zero_iff_eq_zero_or_one]; tauto
    rcases (show Ω n = 1 ∨ Ω n = 2 by omega) with h | h
    · exact Or.inl (ArithmeticFunction.cardFactors_eq_one_iff_prime.mp h)
    · right
      have hmp : n.minFac.Prime := Nat.minFac_prime h1
      have hdec : n = n.minFac * (n / n.minFac) := (Nat.mul_div_cancel' (Nat.minFac_dvd n)).symm
      have hq0 : n / n.minFac ≠ 0 := by
        intro hq; rw [hq, mul_zero] at hdec; exact h0 hdec
      have hq : Ω (n / n.minFac) = 1 := by
        have := h
        rw [hdec, ArithmeticFunction.cardFactors_mul hmp.ne_zero hq0,
          ArithmeticFunction.cardFactors_apply_prime hmp] at this
        omega
      exact ⟨n.minFac, n / n.minFac, hmp,
        ArithmeticFunction.cardFactors_eq_one_iff_prime.mp hq, hdec⟩

/-- `P_x(1,2) ≤ D_{1,2}(x)`: Chen's count is at most the lab's `D12`. -/
theorem chenP_le_D12 (x : ℕ) : chenP x ≤ D12 x := by
  classical
  unfold chenP D12
  apply card_le_card
  intro p hp
  simp only [mem_filter, mem_range] at hp ⊢
  exact ⟨by omega, hp.2.1, ((chenRep_iff _).mp hp.2.2).1.2⟩

/-- `D_{1,2}(x) ≤ P_x(1,2) + 1` for even `x ≥ 4`: the lab's `D12` also counts `x - p = 1`,
the only extra case, at most one prime `p = x - 1`. -/
theorem D12_le_chenP_add_one (x : ℕ) (hx : Even x) (h4 : 4 ≤ x) : D12 x ≤ chenP x + 1 := by
  classical
  unfold chenP D12
  calc #{p ∈ range (x + 1) | p.Prime ∧ Ω (x - p) ≤ 2}
      ≤ #(insert (x - 1) {p ∈ range x | p.Prime ∧ ChenRep (x - p)}) := by
        apply card_le_card
        intro p hp
        simp only [mem_filter, mem_range] at hp
        obtain ⟨hpx, hp, hΩ⟩ := hp
        rw [mem_insert, mem_filter, mem_range]
        by_cases h1 : x - p = 1
        · left; omega
        · right
          have hpne : p ≠ x := by
            rintro rfl
            have := (Nat.Prime.even_iff hp).mp hx; omega
          refine ⟨by omega, hp, (chenRep_iff _).mpr ⟨⟨by omega, hΩ⟩, h1⟩⟩
    _ ≤ _ := card_insert_le _ _

/-- `P_x(1,2) ≤ chenCount x`, the lab's count of `p < x` with `x - p` an `IsAtMostAlmostPrime 2`. -/
theorem chenP_le_chenCount (x : ℕ) : chenP x ≤ chenCount x := by
  classical
  unfold chenP chenCount
  apply card_le_card
  intro p hp
  simp only [mem_filter, mem_range] at hp ⊢
  exact ⟨hp.1, hp.2.1, ((chenRep_iff _).mp hp.2.2).1⟩

/-- `chenCount x ≤ P_x(1,2) + 1`, the extra case again `x - p = 1`. -/
theorem chenCount_le_chenP_add_one (x : ℕ) : chenCount x ≤ chenP x + 1 := by
  classical
  unfold chenP chenCount
  calc #{p ∈ range x | p.Prime ∧ Nat.IsAtMostAlmostPrime 2 (x - p)}
      ≤ #(insert (x - 1) {p ∈ range x | p.Prime ∧ ChenRep (x - p)}) := by
        apply card_le_card
        intro p hp
        simp only [mem_filter, mem_range] at hp
        rw [mem_insert, mem_filter, mem_range]
        by_cases h1 : x - p = 1
        · left; omega
        · right; exact ⟨hp.1, hp.2.1, (chenRep_iff _).mpr ⟨hp.2.2, h1⟩⟩
    _ ≤ _ := card_insert_le _ _

/-- **Chen 1973, Theorem I, in Chen's own form**: for every sufficiently large even `x`,
`P_x(1,2) ≥ 0.67 x C_x / (log x)²`, with `C_x` the lab's `CN x` (no factor 2). -/
def ChenTheoremI : Prop :=
  ∃ x₀ : ℕ, ∀ x : ℕ, Even x → x₀ ≤ x → 0.67 * Θ x ≤ chenP x

/-- Chen's own Theorem I implies the lab's `Chen1973Quant`, which counts with `D12`. -/
theorem chen1973Quant_of_theoremI (h : ChenTheoremI) : Chen1973.Chen1973Quant := by
  obtain ⟨x₀, hx⟩ := h
  refine ⟨x₀, fun x he hle => (hx x he hle).trans ?_⟩
  exact_mod_cast chenP_le_D12 x

/-- Conversely `Chen1973Quant` gives Chen's form up to the single term `x - p = 1`. -/
theorem theoremI_sub_one_of_chen1973Quant (h : Chen1973.Chen1973Quant) :
    ∃ x₀ : ℕ, ∀ x : ℕ, Even x → x₀ ≤ x → 0.67 * Θ x - 1 ≤ chenP x := by
  obtain ⟨x₀, hx⟩ := h
  refine ⟨max x₀ 4, fun x he hle => ?_⟩
  have h1 := hx x he (le_of_max_le_left hle)
  have h2 : (D12 x : ℝ) ≤ chenP x + 1 := by
    exact_mod_cast D12_le_chenP_add_one x he (le_of_max_le_right hle)
  linarith

/-- Vacuity check of `ChenRep`: `7` is counted, `8 = 2·2·2` is not. -/
example : ChenRep 7 ∧ ¬ ChenRep 8 := by
  refine ⟨Or.inl (by norm_num), ?_⟩
  rw [chenRep_iff]
  rintro ⟨⟨_, h⟩, _⟩
  have : Ω 8 = 3 := by
    rw [show (8 : ℕ) = 2 * 4 by rfl, ArithmeticFunction.cardFactors_mul (by norm_num) (by norm_num),
      show (4 : ℕ) = 2 * 2 by rfl, ArithmeticFunction.cardFactors_mul (by norm_num) (by norm_num),
      ArithmeticFunction.cardFactors_apply_prime Nat.prime_two]
  omega

/-! ### 2. Lemma 9, display (33) -/

/-- **The elementary inequality under (33)**: `log x ≤ (x-1)/2 + (x-1)/(1+x)`. Chen states it
for `1 ≤ x ≤ 2`; it holds for every `x ≥ 1`, since the derivative of the difference is
`(x-1)(x²+x+2) / (2x(1+x)²) ≥ 0`. -/
theorem log_le_chen33 {x : ℝ} (hx : 1 ≤ x) : log x ≤ (x - 1) / 2 + (x - 1) / (1 + x) := by
  let g : ℝ → ℝ := fun t => (t - 1) / 2 + (t - 1) / (1 + t) - log t
  have hd : ∀ t : ℝ, 0 < t → HasDerivAt g (1 / 2 + 2 / (1 + t) ^ 2 - 1 / t) t := by
    intro t ht
    have h1t : (1 + t) ≠ 0 := by linarith
    have hA : HasDerivAt (fun t : ℝ => (t - 1) / 2) (1 / 2) t := by
      simpa using ((hasDerivAt_id t).sub_const 1).div_const 2
    have hB : HasDerivAt (fun t : ℝ => (t - 1) / (1 + t)) (2 / (1 + t) ^ 2) t := by
      have := ((hasDerivAt_id' t).sub_const 1).div ((hasDerivAt_id' t).const_add 1) h1t
      convert this using 1
      field_simp; ring
    have hC : HasDerivAt log (1 / t) t := by simpa using Real.hasDerivAt_log ht.ne'
    exact (hA.add hB).sub hC
  have hmono : MonotoneOn g (Set.Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · intro t ht
      exact (hd t (by simp at ht; linarith)).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      exact (hd t (by simp at ht; linarith)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht1 : 1 < t := ht
      rw [(hd t (by linarith)).deriv]
      have h0 : 0 < t := by linarith
      have key : 1 / 2 + 2 / (1 + t) ^ 2 - 1 / t =
          (t - 1) * (t ^ 2 + t + 2) / (2 * t * (1 + t) ^ 2) := by
        field_simp; ring
      rw [key]
      apply div_nonneg
      · apply mul_nonneg (by linarith); nlinarith
      · positivity
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  simp only [g, sub_self, zero_div, log_one, add_zero] at this
  linarith

/-- **Integrand identity of (33)**: `(2.5-u)/(2u(5-u)) · (u - 3 + 4/(u-1) - 2)` equals
`1/2 - 2.25/u - 1/(4(5-u)) + 0.75/(u-1)`, for `u ∉ {0, 1, 5}`. -/
theorem chen33_integrand {u : ℝ} (h0 : u ≠ 0) (h1 : u - 1 ≠ 0) (h5 : 5 - u ≠ 0) :
    (2.5 - u) / (2 * u * (5 - u)) * (u - 3 + 4 / (u - 1) - 2) =
      1 / 2 - 2.25 / u - 1 / (4 * (5 - u)) + 0.75 / (u - 1) := by
  field_simp
  ring

/-- **Inner integral of (33)**: `∫₂^v ((t-2)/2 + (t-2)/t) dt/t = (v - 4 + 4/v)/2`, which with
`v = u - 1` is Chen's factor `(u - 3 + 4/(u-1) - 2)/2`. -/
theorem chen33_inner {v : ℝ} (hv : 2 ≤ v) :
    ∫ t in (2 : ℝ)..v, ((t - 2) / 2 + (t - 2) / t) / t = (v - 4 + 4 / v) / 2 := by
  have hF : ∀ t ∈ Set.uIcc (2 : ℝ) v,
      HasDerivAt (fun t : ℝ => t / 2 + 2 * t⁻¹)
        (((t - 2) / 2 + (t - 2) / t) / t) t := by
    intro t ht
    rw [Set.uIcc_of_le hv] at ht
    have htp : 0 < t := by linarith [ht.1]
    have := ((hasDerivAt_id' t).div_const 2).add ((hasDerivAt_inv htp.ne').const_mul 2)
    convert this using 1
    field_simp; ring
  have hcont : ContinuousOn (fun t : ℝ => ((t - 2) / 2 + (t - 2) / t) / t) (Set.uIcc 2 v) := by
    intro t ht
    rw [Set.uIcc_of_le hv] at ht
    have htp : t ≠ 0 := by linarith [ht.1]
    exact (((continuousAt_id.sub continuousAt_const).div_const 2).add
      ((continuousAt_id.sub continuousAt_const).div continuousAt_id htp)).div
      continuousAt_id htp |>.continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF (hcont.intervalIntegrable)]
  have hv0 : v ≠ 0 := by linarith
  field_simp
  ring

/-- **Outer integral of (33)**: `∫₃⁴ (1/2 - 2.25/u - 1/(4(5-u)) + 0.75/(u-1)) du`
`= 1/2 - 2.25 log(4/3) - log 2 / 4 + 0.75 log(3/2)`, Chen's closed form. -/
theorem chen33_outer :
    ∫ u in (3 : ℝ)..4, (1 / 2 - 2.25 / u - 1 / (4 * (5 - u)) + 0.75 / (u - 1)) =
      1 / 2 - 2.25 * log (4 / 3) - log 2 / 4 + 0.75 * log (3 / 2) := by
  have hF : ∀ u ∈ Set.uIcc (3 : ℝ) 4,
      HasDerivAt (fun u : ℝ => u / 2 - 2.25 * log u + log (5 - u) / 4 + 0.75 * log (u - 1))
        (1 / 2 - 2.25 / u - 1 / (4 * (5 - u)) + 0.75 / (u - 1)) u := by
    intro u hu
    rw [Set.uIcc_of_le (by norm_num)] at hu
    have hu0 : u ≠ 0 := by linarith [hu.1]
    have hu5 : 5 - u ≠ 0 := by linarith [hu.2]
    have hu1 : u - 1 ≠ 0 := by linarith [hu.1]
    have h5 : HasDerivAt (fun u : ℝ => 5 - u) (-1) u := by
      simpa using (hasDerivAt_id u).const_sub 5
    have h1 : HasDerivAt (fun u : ℝ => u - 1) 1 u := by
      simpa using (hasDerivAt_id u).sub_const 1
    have := ((((hasDerivAt_id' u).div_const 2).sub ((Real.hasDerivAt_log hu0).const_mul 2.25)).add
      ((h5.log hu5).div_const 4)).add ((h1.log hu1).const_mul 0.75)
    convert this using 1
    field_simp
    ring
  have hcont : ContinuousOn (fun u : ℝ => 1 / 2 - 2.25 / u - 1 / (4 * (5 - u)) + 0.75 / (u - 1))
      (Set.uIcc 3 4) := by
    intro u hu
    rw [Set.uIcc_of_le (by norm_num)] at hu
    have hu0 : u ≠ 0 := by linarith [hu.1]
    have hu5 : 4 * (5 - u) ≠ 0 := by have := hu.2; intro h; linarith
    have hu1 : u - 1 ≠ 0 := by linarith [hu.1]
    exact ((((continuousAt_const.sub (continuousAt_const.div continuousAt_id hu0))).sub
      (continuousAt_const.div (continuousAt_const.mul (continuousAt_const.sub continuousAt_id))
        hu5)).add
      (continuousAt_const.div (continuousAt_id.sub continuousAt_const) hu1)).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF hcont.intervalIntegrable]
  have e1 : log (4 / 3) = log 4 - log 3 := log_div (by norm_num) (by norm_num)
  have e2 : log (3 / 2) = log 3 - log 2 := log_div (by norm_num) (by norm_num)
  have e3 : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; norm_num
  norm_num [e1, e2, e3]
  ring

/-- Chen's rewriting of the closed form, `1/2 + 0.75 log(9/8) - 1.5 log(4/3) - log 2/4`, in
terms of `log 2`, `log 3`: it equals `1/2 + 3 log 3 - (11/2) log 2`. -/
theorem chen33_closed :
    1 / 2 - 2.25 * log (4 / 3) - log 2 / 4 + 0.75 * log (3 / 2) =
      1 / 2 + 0.75 * log (9 / 8) - 1.5 * log (4 / 3) - log 2 / 4 ∧
    1 / 2 + 0.75 * log (9 / 8) - 1.5 * log (4 / 3) - log 2 / 4 =
      1 / 2 + 3 * log 3 - 11 / 2 * log 2 := by
  have e1 : log (4 / 3) = 2 * log 2 - log 3 := by
    rw [log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; norm_num
  have e2 : log (3 / 2) = log 3 - log 2 := log_div (by norm_num) (by norm_num)
  have e3 : log (9 / 8) = 2 * log 3 - 3 * log 2 := by
    rw [log_div (by norm_num) (by norm_num), show (9 : ℝ) = 3 ^ 2 by norm_num,
      show (8 : ℝ) = 2 ^ 3 by norm_num, log_pow, log_pow]; norm_num
  rw [e1, e2, e3]
  constructor <;> ring

/-- **Value of the closed form of (33)**, the QUESTION: `-0.0164727 < v < -0.0164725` where
`v = 1/2 + 3 log 3 - (11/2) log 2`. Chen prints `v ≥ 0.588335 - 0.6048075 = -0.0164725`,
which the upper bound here contradicts by about `1.3·10⁻⁷`; a rounding slip, see the file
header. -/
theorem chen33_value_bounds :
    -0.0164727 < 1 / 2 + 3 * log 3 - 11 / 2 * log 2 ∧
      1 / 2 + 3 * log 3 - 11 / 2 * log 2 < -0.0164725 := by
  have l2a := log_two_gt_d9
  have l2b := log_two_lt_d9
  have l3a := log_three_gt_d9
  have l3b := log_three_lt_d9
  constructor <;> norm_num at * <;> linarith

/-- **Lemma 9 margin, with the true value of (33)**: `0.3301 ≤ log 4 - log 8 / 2 + v`, so
Chen's `8 · 0.3301 = 2.6408` survives the rounding slip. -/
theorem lemma9_margin :
    0.3301 ≤ log 4 - log 8 / 2 + (1 / 2 + 3 * log 3 - 11 / 2 * log 2) := by
  have e4 : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; norm_num
  have e8 : log (8 : ℝ) = 3 * log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, log_pow]; norm_num
  have := (chen33_value_bounds).1
  have l2a := log_two_gt_d9
  rw [e4, e8]
  norm_num at *
  linarith

/-! ### 3. The constants of Lemmas 8, 9 and display (34) -/

/-- Lemma 8: `8 · 0.49254 = 3.94032 ≤ 3.9404`, from (27) and (28). -/
theorem lemma8_const : (8 : ℝ) * 0.49254 ≤ 3.9404 := by norm_num

/-- Lemma 9: `8 · 0.3301 = 2.6408`. -/
theorem lemma9_const : (8 : ℝ) * 0.3301 = 2.6408 := by norm_num

/-- Section III: `2.6408 - 3.9404 / 2 = 0.6706 ≥ 0.67`. -/
theorem final_const : (0.67 : ℝ) ≤ 2.6408 - 3.9404 / 2 := by norm_num

/-- **Assembly of (34)**, in any unit `T = x C_x / (log x)²`: if
`P ≥ A - S/2 - Ω/2 - E` (display (34)), `A - S/2 ≥ (2.6408 - δ) T` (Lemma 9),
`Ω ≤ (3.9404 + δ) T` (Lemma 8), `E ≤ δ T`, and `δ ≤ 0.0002`, then `P ≥ 0.67 T`.
Pure algebra; Lemmas 8, 9 and (34) are the analytic content, not proved here. -/
theorem assembly34 (T δ P A S Q E : ℝ) (h34 : A - S / 2 - Q / 2 - E ≤ P)
    (h9 : (2.6408 - δ) * T ≤ A - S / 2) (h8 : Q ≤ (3.9404 + δ) * T) (hE : E ≤ δ * T)
    (hT : 0 ≤ T) (hδ : δ ≤ 0.0002) : 0.67 * T ≤ P := by
  nlinarith

/-- Vacuity of `assembly34`: `T = 1`, `δ = 0`, `A = 2.6408`, `S = 0`, `Q = 3.9404`, `E = 0`,
`P = 0.6706`. -/
example : 0.67 * (1 : ℝ) ≤ 0.6706 :=
  assembly34 1 0 0.6706 2.6408 0 3.9404 0 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-! ### 4. Lemma 7, the bookkeeping identity before (24) -/

open scoped Nat ArithmeticFunction.omega ArithmeticFunction.zeta
open ArithmeticFunction

/-- `φ(lcm(a,b)) φ(gcd(a,b)) = φ(a) φ(b)`, for `a, b ≠ 0`. -/
theorem totient_lcm_mul_totient_gcd {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    φ (a.lcm b) * φ (a.gcd b) = φ a * φ b := by
  have hg0 : a.gcd b ≠ 0 := Nat.gcd_ne_zero_left ha
  have hgl : a.gcd b ∣ a.lcm b := (Nat.gcd_dvd_left a b).trans (Nat.dvd_lcm_left a b)
  -- `φ(g l) = g φ(l)` for `g ∣ l`
  have key := Nat.totient_gcd_mul_totient_mul (a.gcd b) (a.lcm b)
  rw [Nat.gcd_eq_left hgl] at key
  have hφg : 0 < φ (a.gcd b) := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hg0)
  have h1 : φ (a.gcd b * a.lcm b) = φ (a.lcm b) * a.gcd b := by
    have := key
    rw [mul_assoc] at this
    exact Nat.eq_of_mul_eq_mul_left hφg this
  have h2 := Nat.totient_gcd_mul_totient_mul a b
  rw [← Nat.gcd_mul_lcm a b, h1] at h2
  have hg : 0 < a.gcd b := Nat.pos_of_ne_zero hg0
  apply Nat.eq_of_mul_eq_mul_right hg
  calc φ (a.lcm b) * φ (a.gcd b) * a.gcd b = φ (a.gcd b) * (φ (a.lcm b) * a.gcd b) := by ring
    _ = φ a * φ b * a.gcd b := h2

/-- For squarefree `n`, `φ n = ∏_{p ∣ n} (p - 1)`. -/
theorem totient_eq_prod_of_squarefree {n : ℕ} (hn : Squarefree n) :
    (φ n : ℤ) = ∏ p ∈ n.primeFactors, ((p : ℤ) - 1) := by
  have h := Nat.totient_mul_prod_primeFactors n
  rw [Nat.prod_primeFactors_of_squarefree hn] at h
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn.ne_zero
  have h' : φ n = ∏ p ∈ n.primeFactors, (p - 1) := by
    rw [mul_comm] at h; exact Nat.eq_of_mul_eq_mul_left hn0 h
  rw [h', Nat.cast_prod]
  refine prod_congr rfl fun p hp => ?_
  have := (Nat.prime_of_mem_primeFactors hp).one_le
  push_cast [this]; ring

/-- **Chen's divisor sum, Lemma 7 before (24)**: for squarefree `n`,
`∑_{d ∣ n} f(d) = φ(n)`, where on squarefree `d` Chen's `f(d) = φ(d) ∏_{p∣d} (p-2)/(p-1)`
is `∏_{p ∣ d} (p - 2)`. -/
theorem sum_divisors_prod_sub_two {n : ℕ} (hn : Squarefree n) :
    ∑ d ∈ n.divisors, ∏ p ∈ d.primeFactors, ((p : ℤ) - 2) = φ n := by
  have h := IsMultiplicative.prodPrimeFactors_add_of_squarefree
    (IsMultiplicative.prodPrimeFactors (fun p : ℕ => (p : ℤ) - 2))
    (isMultiplicative_zeta.natCast (R := ℤ)) hn
  rw [coe_mul_zeta_apply, prodPrimeFactors_apply hn.ne_zero] at h
  have hl : ∀ p ∈ n.primeFactors,
      ((prodPrimeFactors fun p : ℕ => (p : ℤ) - 2) + (ζ : ArithmeticFunction ℤ)) p =
        (p : ℤ) - 1 := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    rw [ArithmeticFunction.add_apply, prodPrimeFactors_apply hpp.ne_zero, hpp.primeFactors, prod_singleton,
      natCoe_apply, zeta_apply, if_neg hpp.ne_zero]
    push_cast; ring
  rw [prod_congr rfl hl, ← totient_eq_prod_of_squarefree hn] at h
  rw [h]
  exact sum_congr rfl fun d hd => (prodPrimeFactors_apply (Nat.pos_of_mem_divisors hd).ne').symm

/-- **Chen's identity before (24)**, multiplied out: for squarefree `d₁, d₂`,
`φ(d₁) φ(d₂) = φ(d₁d₂/(d₁,d₂)) ∑_{d ∣ (d₁,d₂)} f(d)`, i.e.
`1/φ(d₁d₂/(d₁,d₂)) = g(d₁) g(d₂) ∑_{d∣(d₁,d₂)} f(d)` with `g = 1/φ`. -/
theorem chen_lcm_identity {d₁ d₂ : ℕ} (h1 : Squarefree d₁) (h2 : Squarefree d₂) :
    ((φ d₁ * φ d₂ : ℕ) : ℤ) =
      φ (d₁ * d₂ / d₁.gcd d₂) * ∑ d ∈ (d₁.gcd d₂).divisors, ∏ p ∈ d.primeFactors, ((p : ℤ) - 2) := by
  rw [sum_divisors_prod_sub_two (h1.squarefree_of_dvd (Nat.gcd_dvd_left d₁ d₂)),
    ← Nat.lcm.eq_1, ← totient_lcm_mul_totient_gcd h1.ne_zero h2.ne_zero]
  push_cast; ring

/-- Chen p. 164: for squarefree `d`, the number of pairs `(d₁, d₂)` with
`d₁d₂/(d₁,d₂) = d` is `3^{ν(d)}`. HELPER: Mathlib's `Nat.card_pair_lcm_eq`, restated. -/
theorem chen_card_pairs {d : ℕ} (hd : Squarefree d) :
    #{p ∈ d.divisors ×ˢ d.divisors | p.1 * p.2 / p.1.gcd p.2 = d} = 3 ^ ω d := by
  simpa [← Nat.lcm.eq_1] using Nat.card_pair_lcm_eq hd

end LeanLab.AlmostPrimeSums.Chen1973Own
