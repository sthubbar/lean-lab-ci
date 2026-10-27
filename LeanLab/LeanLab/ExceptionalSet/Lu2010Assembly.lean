/-
P0095 W. C. Lu, Exceptional set of Goldbach number, J. Number Theory 130 (2010) 2359-2392.
Unit U-6842, CLOUD MANUAL-M1, 2026-10-21, track T1. Read from the version of record,
papers/P0095.pdf, pages 2360 to 2362 and 2390 to 2392 rendered as page images.

Section 10 ends: "Combining Lemma 1, (9), (84), (85), (86) and the result of Section 9 we may
easily obtain Theorem. E(x) ≪ x^0.879." The combination is not written in the paper. This file
writes it, with the paper's parameters:
* d = N^0.9999, a = N^0.0001 / 3, b = N/d - a, p. 2360;
* P = N^c with c = 0.1215, p. 2360, the only value of c the paper prints;
* Lemma 1 holds for |k - N| ≤ d N^-0.00011, the window `Win N` below; (84), (85), (86) hold on
  the larger window |k - N| ≤ d N^-0.0001, Section 9 sums over every k.

The paper's analytic estimates enter as one bundle `Inputs`, each field a printed display,
restricted to `Win N`, which only weakens it. `D N k`, the paper's (1), is defined here
concretely, and its smallness at a non-Goldbach even k is PROVED, not assumed.

Result, CONDITIONAL ON `Inputs`: every dyadic block holds at most C Y^0.8789126 exceptions, so
E X ≪ X^0.8789126 and E X < X^0.879 for all large X, the paper's Theorem in the eventual form
that Pintz 2018 eq (1.8) reports. Bookkeeping: per window the exceptions number
≪ N^{1.0002 - c + 2η}, (86) dominating Section 9, with η = 1.3e-6 covering the P^-0.00001 loss
of (85); a dyadic block needs ≪ Y^0.00021 windows because Lemma 1's window is that short.
The margin below 0.879 is 8.74e-5; with c = 0.121 the same count gives 0.8794 and fails,
so the paper's 0.879 needs c = 0.1215 to its fourth digit, see numerics/lu2010_assembly_M1.py.

AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel.
Binary Goldbach itself is OPEN; this is an almost-all bound.
-/
import Mathlib
import LeanLab.ExceptionalSet.Lu2010
import LeanLab.ExceptionalSet.Li2000
import LeanLab.ExceptionalSet.PintzAlthofer2026Major

namespace LeanLab.ExceptionalSet.Lu2010Assembly
open Real Filter Topology Finset ArithmeticFunction LeanLab.ExceptionalSet
  LeanLab.ExceptionalSet.Pintz2018Reduction
open LeanLab.ExceptionalSet.PintzAlthofer2026 (RΛ RΛ_le_of_not_goldbach)

/-! ### The paper's parameters, p. 2360 -/

/-- `c = 0.1215`, `P = N^c`. -/
noncomputable def c : ℝ := 0.1215

/-- `d = N^0.9999`. -/
noncomputable def dd (N : ℕ) : ℝ := (N : ℝ) ^ (0.9999 : ℝ)

/-- `a = N^0.0001 / 3`. -/
noncomputable def aa (N : ℕ) : ℝ := (N : ℝ) ^ (0.0001 : ℝ) / 3

/-- `b = N/d - a`. -/
noncomputable def bb (N : ℕ) : ℝ := N / dd N - aa N

/-- `P = N^c`. -/
noncomputable def PP (N : ℕ) : ℝ := (N : ℝ) ^ c

/-- Lemma 1's window radius `d N^-0.00011`, rounded down. -/
noncomputable def rad (N : ℕ) : ℕ := ⌊dd N * (N : ℝ) ^ (-0.00011 : ℝ)⌋₊

/-- The integers `k` with `|k - N| ≤ d N^-0.00011`. -/
noncomputable def Win (N : ℕ) : Finset ℕ := Icc (N - rad N) (N + rad N)

/-- The paper's (1): `D(k) = Σ_{ad+d < n ≤ bd} Λ(n) Λ(k-n)`. Truncated subtraction makes the
terms with `n > k` zero, as `Λ 0 = 0`. -/
noncomputable def DLu (N k : ℕ) : ℝ :=
  ∑ n ∈ Ioc ⌊aa N * dd N + dd N⌋₊ ⌊bb N * dd N⌋₊, Λ n * Λ (k - n)

/-- The exceptions in Lemma 1's window around `N`. -/
noncomputable def bad (N : ℕ) : Finset ℕ := by
  classical exact (Win N).filter Exc

/-! ### Elementary facts, PROVED -/

theorem rad_eq (N : ℕ) (hN : 0 < N) : dd N * (N : ℝ) ^ (-0.00011 : ℝ) = (N : ℝ) ^ (0.99979 : ℝ) := by
  unfold dd
  rw [← rpow_add (by exact_mod_cast hN)]; norm_num

/-- `(b - a) d = N/3`. -/
theorem bad_mul (N : ℕ) (hN : 0 < N) : (bb N - aa N) * dd N = N / 3 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hd : 0 < dd N := rpow_pos_of_pos hN' _
  have h1 : (N : ℝ) ^ (0.0001 : ℝ) * dd N = N := by
    unfold dd; rw [← rpow_add hN']; norm_num
  unfold bb aa
  field_simp
  nlinarith [h1]

/-- `D(k) ≤ R_Λ(k)`: the paper's sum is a sub-sum of the full convolution. -/
theorem DLu_le_RΛ (N k : ℕ) : DLu N k ≤ RΛ k := by
  unfold DLu RΛ
  have hnn : ∀ n, 0 ≤ Λ n * Λ (k - n) := fun n => mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg
  rw [← Finset.sum_filter_of_ne (p := fun n => n ≤ k)]
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [Finset.mem_filter] at hn
      simp only [Finset.mem_range]; omega
    · intro n _ _; exact hnn n
  · intro n _ hne
    by_contra hlt
    rw [not_le] at hlt
    have : k - n = 0 := by omega
    rw [this] at hne; simp at hne

/-- A non-Goldbach `k ≥ 1` has `D(k) ≤ 8·10^6 k^0.53`, from the proper prime power count. -/
theorem DLu_le_of_not_goldbach (N : ℕ) {k : ℕ} (hk : 1 ≤ k) (hng : ¬ IsGoldbachSum k) :
    DLu N k ≤ 8000000 * (k : ℝ) ^ (0.53 : ℝ) := by
  have h1 := (DLu_le_RΛ N k).trans (RΛ_le_of_not_goldbach hng)
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := by linarith
  have hlog0 : 0 ≤ Real.log k := Real.log_nonneg hk'
  -- log k ≤ 100 k^0.01
  have hlog : Real.log k ≤ 100 * (k : ℝ) ^ (0.01 : ℝ) := by
    have := Real.log_le_rpow_div hk0 (ε := 0.01) (by norm_num)
    linarith [show (k : ℝ) ^ (0.01 : ℝ) / 0.01 = 100 * (k : ℝ) ^ (0.01 : ℝ) by ring]
  -- Nat.log 2 k ≤ 2 log k
  have hnl : (Nat.log 2 k : ℝ) ≤ 2 * Real.log k := by
    have h := Real.natLog_le_logb k 2
    have hl2 : (0.5 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have : Real.logb 2 k ≤ 2 * Real.log k := by
      rw [Real.logb, div_le_iff₀ (by linarith)]
      nlinarith
    exact_mod_cast h.trans this
  -- √k + 1 ≤ 2 k^(1/2)
  have hsq : ((Nat.sqrt k : ℕ) : ℝ) + 1 ≤ 2 * (k : ℝ) ^ (0.5 : ℝ) := by
    have hs : ((Nat.sqrt k : ℕ) : ℝ) ≤ Real.sqrt k := Real.nat_sqrt_le_real_sqrt
    have hs' : Real.sqrt k = (k : ℝ) ^ (0.5 : ℝ) := by
      rw [Real.sqrt_eq_rpow]; norm_num
    have : (1 : ℝ) ≤ (k : ℝ) ^ (0.5 : ℝ) := Real.one_le_rpow hk' (by norm_num)
    linarith
  have hp1 : (0 : ℝ) ≤ (k : ℝ) ^ (0.01 : ℝ) := rpow_nonneg hk0 _
  have hp5 : (0 : ℝ) ≤ (k : ℝ) ^ (0.5 : ℝ) := rpow_nonneg hk0 _
  have hcast : (((Nat.sqrt k + 1) * Nat.log 2 k : ℕ) : ℝ) =
      ((Nat.sqrt k : ℕ) + 1 : ℝ) * (Nat.log 2 k : ℝ) := by push_cast; ring
  rw [hcast] at h1
  have hnl0 : (0 : ℝ) ≤ Nat.log 2 k := Nat.cast_nonneg _
  have hA : ((Nat.sqrt k : ℕ) + 1 : ℝ) * (Nat.log 2 k : ℝ) ≤
      (2 * (k : ℝ) ^ (0.5 : ℝ)) * (200 * (k : ℝ) ^ (0.01 : ℝ)) := by
    apply mul_le_mul hsq (by linarith) hnl0 (by positivity)
  have hB : Real.log k ^ 2 ≤ (100 * (k : ℝ) ^ (0.01 : ℝ)) ^ 2 := by
    exact pow_le_pow_left₀ hlog0 hlog 2
  have hprod : (k : ℝ) ^ (0.5 : ℝ) * (k : ℝ) ^ (0.01 : ℝ) * ((k : ℝ) ^ (0.01 : ℝ)) ^ 2 =
      (k : ℝ) ^ (0.53 : ℝ) := by
    rw [← rpow_natCast, ← rpow_mul hk0, ← rpow_add (by linarith), ← rpow_add (by linarith)]
    norm_num
  have hAB : 2 * (((Nat.sqrt k : ℕ) + 1 : ℝ) * (Nat.log 2 k : ℝ)) * Real.log k ^ 2 ≤
      2 * ((2 * (k : ℝ) ^ (0.5 : ℝ)) * (200 * (k : ℝ) ^ (0.01 : ℝ))) *
        (100 * (k : ℝ) ^ (0.01 : ℝ)) ^ 2 := by
    apply mul_le_mul (by linarith) hB (by positivity) (by positivity)
  calc DLu N k ≤ _ := h1
    _ ≤ _ := hAB
    _ = 8000000 * ((k : ℝ) ^ (0.5 : ℝ) * (k : ℝ) ^ (0.01 : ℝ) * ((k : ℝ) ^ (0.01 : ℝ)) ^ 2) := by
        ring
    _ = 8000000 * (k : ℝ) ^ (0.53 : ℝ) := by rw [hprod]

/-! ### The cited input, Lu's displays -/

/-- **Cited input**, Lu 2010, the displays the Theorem combines, restricted to `Win N`:
* `lemma1`: Lemma 1 with (9), `D(k) = D₁(k) + D₂(k) + O(N^{0.99995})`, weaker than the printed
  `O(N^{1-0.0001})`, which the printed proof does not deliver, see Lu2010Lemma1 Q-6843a;
* `lower`: for each large `N` either (84) or (85) holds on the window, with the `O` terms
  written as `- Cerr ·`; `𝔖(k) ≥ 1` for even `k`, true for the singular series;
* `sec9`: Section 9, `Σ_k |D₂(k)|² ≪ N^{3-c+0.00011}`;
* `eq86`: (86), `Σ |D₆(k)|² ≪ P^{-1} d N^{2.0003}`.
`D₁` is real in (84) and (85); `D₂` and `D₆` are complex. -/
structure Inputs where
  D1 : ℕ → ℕ → ℝ
  D2 : ℕ → ℕ → ℂ
  D6 : ℕ → ℕ → ℂ
  S : ℕ → ℝ
  S_ge : ∀ k, Even k → 1 ≤ S k
  N0 : ℕ
  C1 : ℝ
  Cerr : ℝ
  c1 : ℝ
  c1_pos : 0 < c1
  C9 : ℝ
  C86 : ℝ
  lemma1 : ∀ N, N0 ≤ N → ∀ k ∈ Win N,
    ‖(DLu N k : ℂ) - ((D1 N k : ℂ) + D2 N k)‖ ≤ C1 * (N : ℝ) ^ (1 - 0.00005 : ℝ)
  lower : ∀ N, N0 ≤ N →
    (∀ k ∈ Win N, Even k →
      S k * (bb N - aa N) * dd N *
        ((Real.log (Real.log (Real.log N)))⁻¹ - Cerr * (Real.log (Real.log N)) ^ (-(1 / 2) : ℝ))
        - ‖D6 N k‖ < D1 N k) ∨
    (∀ k ∈ Win N, Even k →
      S k * (bb N - aa N) * dd N * c1 * PP N ^ (-0.00001 : ℝ) * Real.log (PP N) *
        (2 * c⁻¹ - Cerr * (Real.log (Real.log (Real.log N))) ^ (-0.1 : ℝ))
        - ‖D6 N k‖ ≤ D1 N k)
  sec9 : ∀ N, N0 ≤ N → ∑ k ∈ Win N, ‖D2 N k‖ ^ 2 ≤ C9 * (N : ℝ) ^ (3 - c + 0.00011)
  eq86 : ∀ N, N0 ≤ N →
    ∑ k ∈ Win N, ‖D6 N k‖ ^ 2 ≤ C86 * PP N ^ (-1 : ℝ) * dd N * (N : ℝ) ^ (2.0003 : ℝ)

/-- `η = 1.3·10^{-6}`, the main term loss allowed; it exceeds `c · 10^{-5}` from (85). -/
noncomputable def η : ℝ := 0.0000013

/-! ### The main terms beat `N^{1-η}`, PROVED -/

/-- Eventually `(log log log x)⁻¹ - C (log log x)^{-1/2} ≥ 3 x^{-η}`, the bracket of (84). -/
theorem bracket84_eventually (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, 3 * x ^ (-η) ≤
      (Real.log (Real.log (Real.log x)))⁻¹ - C * (Real.log (Real.log x)) ^ (-(1 / 2) : ℝ) := by
  have hη : (0 : ℝ) < η := by unfold η; norm_num
  have hll : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_log_atTop
  have hlll : Tendsto (fun x : ℝ => Real.log (Real.log (Real.log x))) atTop atTop :=
    tendsto_log_atTop.comp hll
  -- log u ≤ u^{1/2} / (2|C| + 1) for large u
  have hA : ∀ᶠ u : ℝ in atTop, Real.log u ≤ (2 * |C| + 1)⁻¹ * u ^ (1 / 2 : ℝ) := by
    have h := (isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).bound
      (c := (2 * |C| + 1)⁻¹) (by positivity)
    filter_upwards [h, eventually_ge_atTop 1] with u hu hu1
    have h0 : 0 ≤ Real.log u := Real.log_nonneg hu1
    rw [Real.norm_of_nonneg h0, Real.norm_of_nonneg (rpow_nonneg (by linarith) _)] at hu
    exact hu
  -- log x ≤ x^{η/2} and x^{η/2} ≥ 6 eventually, so log x ≤ x^η / 6
  have hB : ∀ᶠ x : ℝ in atTop, Real.log x ≤ (1 / 6) * x ^ η := by
    have h := (isLittleO_log_rpow_atTop hη).bound (c := 1 / 6) (by norm_num)
    filter_upwards [h, eventually_ge_atTop 1] with x hx hx1
    rw [Real.norm_of_nonneg (Real.log_nonneg hx1),
      Real.norm_of_nonneg (rpow_nonneg (by linarith) _)] at hx
    exact hx
  filter_upwards [hll.eventually hA, hB, hlll.eventually (eventually_gt_atTop 0),
    hll.eventually (eventually_gt_atTop 1), eventually_gt_atTop 1,
    tendsto_log_atTop.eventually (eventually_gt_atTop 1)] with x hAx hBx h3 h2 hx1 h1
  set u := Real.log (Real.log x) with hu
  set w := Real.log u with hw
  have hu0 : 0 < u := by linarith
  have hsq : 0 < u ^ (1 / 2 : ℝ) := rpow_pos_of_pos hu0 _
  -- w ≤ log x
  have hwl : w ≤ Real.log x := by
    have := Real.log_le_self (le_of_lt hu0)
    have h' : u ≤ Real.log x := Real.log_le_self (by linarith)
    linarith
  have hxη : 0 < x ^ η := rpow_pos_of_pos (by linarith) _
  -- 3 x^{-η} ≤ 1 / (2 w)
  have hneg : x ^ (-η) = (x ^ η)⁻¹ := rpow_neg (by linarith) _
  have h1' : 3 * x ^ (-η) ≤ (2 * w)⁻¹ := by
    rw [hneg]
    rw [show 3 * (x ^ η)⁻¹ = (x ^ η / 3)⁻¹ by field_simp]
    apply inv_anti₀ (by positivity)
    linarith
  -- C u^{-1/2} ≤ 1 / (2 w)
  have hCu : C * u ^ (-(1 / 2) : ℝ) ≤ (2 * w)⁻¹ := by
    rw [rpow_neg hu0.le]
    have hAx' : (2 * |C| + 1) * w ≤ u ^ (1 / 2 : ℝ) := by
      have := mul_le_mul_of_nonneg_left hAx (by positivity : (0 : ℝ) ≤ 2 * |C| + 1)
      rwa [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul] at this
    have hC : C ≤ |C| := le_abs_self C
    rw [← div_eq_mul_inv, div_le_iff₀ hsq, inv_mul_eq_div, le_div_iff₀ (by linarith)]
    nlinarith [abs_nonneg C]
  have hsplit : (2 * w)⁻¹ + (2 * w)⁻¹ = w⁻¹ := by field_simp; ring
  linarith

/-- Eventually `c₁ N^{-c·10^{-5}} c log N (2/c - C (log log log N)^{-0.1}) ≥ 3 N^{-η}`, the
bracket of (85) with `P = N^c`. -/
theorem bracket85_eventually (C c1 : ℝ) (hc1 : 0 < c1) :
    ∀ᶠ x : ℝ in atTop, 3 * x ^ (-η) ≤
      c1 * (x ^ c) ^ (-0.00001 : ℝ) * Real.log (x ^ c) *
        (2 * c⁻¹ - C * (Real.log (Real.log (Real.log x))) ^ (-0.1 : ℝ)) := by
  have hc : c = 0.1215 := rfl
  have hlll : Tendsto (fun x : ℝ => Real.log (Real.log (Real.log x))) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_log_atTop)
  have hdec : Tendsto (fun x : ℝ => (Real.log (Real.log (Real.log x))) ^ (-0.1 : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp hlll
  have hsmall : ∀ᶠ x : ℝ in atTop,
      |C| * (Real.log (Real.log (Real.log x))) ^ (-0.1 : ℝ) ≤ 1 := by
    have : Tendsto (fun x : ℝ => |C| * (Real.log (Real.log (Real.log x))) ^ (-0.1 : ℝ))
        atTop (𝓝 0) := by simpa using hdec.const_mul |C|
    exact this.eventually (ge_mem_nhds (by norm_num))
  -- x^{-(η - c·10^{-5})} → 0
  have hgap : Tendsto (fun x : ℝ => x ^ (-(η - c * 0.00001))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by unfold η; rw [hc]; norm_num)
  have hg : ∀ᶠ x : ℝ in atTop, x ^ (-(η - c * 0.00001)) ≤ c1 / 3 :=
    hgap.eventually (ge_mem_nhds (by positivity))
  filter_upwards [hsmall, hg, eventually_ge_atTop (Real.exp 1),
    hlll.eventually (eventually_gt_atTop 0)] with x hs hgx hx h3
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hlogx : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hx
  have hlc : Real.log (x ^ c) = c * Real.log x := Real.log_rpow hx0 c
  have hpow : (x ^ c) ^ (-0.00001 : ℝ) = x ^ (-(c * 0.00001)) := by
    rw [← rpow_mul hx0.le]; ring_nf
  have hcpos : 0 < c := by rw [hc]; norm_num
  have hci : c⁻¹ ≥ 1 := by rw [hc]; norm_num
  have hlv : 0 ≤ (Real.log (Real.log (Real.log x))) ^ (-0.1 : ℝ) := rpow_nonneg h3.le _
  have hbr : c⁻¹ ≤ 2 * c⁻¹ - C * (Real.log (Real.log (Real.log x))) ^ (-0.1 : ℝ) := by
    have : C * (Real.log (Real.log (Real.log x))) ^ (-0.1 : ℝ) ≤
        |C| * (Real.log (Real.log (Real.log x))) ^ (-0.1 : ℝ) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) hlv
    linarith
  -- c log x · bracket ≥ 1
  have hone : 1 ≤ c * Real.log x * (2 * c⁻¹ - C * (Real.log (Real.log (Real.log x))) ^ (-0.1 : ℝ)) := by
    have : c * Real.log x * c⁻¹ = Real.log x := by field_simp
    have h2 : c * Real.log x * c⁻¹ ≤
        c * Real.log x * (2 * c⁻¹ - C * (Real.log (Real.log (Real.log x))) ^ (-0.1 : ℝ)) :=
      mul_le_mul_of_nonneg_left hbr (by positivity)
    linarith
  have hsplitη : x ^ (-η) = x ^ (-(c * 0.00001)) * x ^ (-(η - c * 0.00001)) := by
    rw [← rpow_add hx0]; ring_nf
  have hq : 0 < x ^ (-(c * 0.00001)) := rpow_pos_of_pos hx0 _
  rw [hpow, hlc, hsplitη]
  calc 3 * (x ^ (-(c * 0.00001)) * x ^ (-(η - c * 0.00001)))
      ≤ 3 * (x ^ (-(c * 0.00001)) * (c1 / 3)) := by gcongr
    _ = c1 * x ^ (-(c * 0.00001)) * 1 := by ring
    _ ≤ c1 * x ^ (-(c * 0.00001)) *
        (c * Real.log x * (2 * c⁻¹ - C * (Real.log (Real.log (Real.log x))) ^ (-0.1 : ℝ))) := by
        gcongr
    _ = _ := by ring

/-! ### Per window count, CONDITIONAL ON `Inputs` -/

/-- From (84) or (85), eventually `D₁(k) ≥ N^{1-η} - |D₆(k)|` on the window, for even `k`. -/
theorem main_eventually (I : Inputs) : ∃ N1 : ℕ, ∀ N, N1 ≤ N → ∀ k ∈ Win N, Even k →
    (N : ℝ) ^ (1 - η) - ‖I.D6 N k‖ ≤ I.D1 N k := by
  have h84 := tendsto_natCast_atTop_atTop.eventually (bracket84_eventually I.Cerr)
  have h85 := tendsto_natCast_atTop_atTop.eventually (bracket85_eventually I.Cerr I.c1 I.c1_pos)
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp (h84.and h85)
  refine ⟨max (max N1 I.N0) 1, fun N hN k hk hke => ?_⟩
  have hN1' : N1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN0 : I.N0 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNpos : 0 < N := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hN)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hNpos
  obtain ⟨b84, b85⟩ := hN1 N hN1'
  have hS := I.S_ge k hke
  have hba := bad_mul N hNpos
  have hNη : (N : ℝ) ^ (1 - η) = N * (N : ℝ) ^ (-η) := by
    rw [sub_eq_add_neg, rpow_add hN', rpow_one]
  have hpos : 0 < (N : ℝ) ^ (-η) := rpow_pos_of_pos hN' _
  rcases I.lower N hN0 with h | h
  · have hk' := h k hk hke
    set B := (Real.log (Real.log (Real.log N)))⁻¹ - I.Cerr * (Real.log (Real.log N)) ^ (-(1 / 2) : ℝ)
    have hB : 0 ≤ B := by linarith
    have : (N : ℝ) ^ (1 - η) ≤ I.S k * (bb N - aa N) * dd N * B := by
      rw [mul_assoc (I.S k), hba, hNη]
      have h3 : (N : ℝ) / 3 * B ≤ I.S k * ((N : ℝ) / 3 * B) :=
        le_mul_of_one_le_left (by positivity) hS
      nlinarith
    linarith
  · have hk' := h k hk hke
    set B := I.c1 * PP N ^ (-0.00001 : ℝ) * Real.log (PP N) *
      (2 * c⁻¹ - I.Cerr * (Real.log (Real.log (Real.log N))) ^ (-0.1 : ℝ))
    have hB : 3 * (N : ℝ) ^ (-η) ≤ B := b85
    have hB0 : 0 ≤ B := by linarith
    have heq : I.S k * (bb N - aa N) * dd N * I.c1 * PP N ^ (-0.00001 : ℝ) * Real.log (PP N) *
        (2 * c⁻¹ - I.Cerr * (Real.log (Real.log (Real.log N))) ^ (-0.1 : ℝ)) =
        I.S k * ((bb N - aa N) * dd N) * B := by simp only [B]; ring
    have : (N : ℝ) ^ (1 - η) ≤ I.S k * ((bb N - aa N) * dd N) * B := by
      rw [hba, hNη]
      have h3 : (N : ℝ) / 3 * B ≤ I.S k * ((N : ℝ) / 3 * B) :=
        le_mul_of_one_le_left (by positivity) hS
      nlinarith
    linarith

/-- `rad N ≤ N`. -/
theorem rad_le (N : ℕ) : rad N ≤ N := by
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0; simp [rad, dd, Real.zero_rpow (by norm_num : (0.9999 : ℝ) ≠ 0)]
  · unfold rad
    rw [rad_eq N hpos]
    apply Nat.floor_le_of_le
    have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hpos
    calc (N : ℝ) ^ (0.99979 : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le h1 (by norm_num)
      _ = N := rpow_one _

/-- The per window exponent `1.0002 - c + 2η = 0.8787026`. -/
noncomputable def θw : ℝ := 0.8787026

/-- Chebyshev: `M ≤ f + g` on `s` with `f, g ≥ 0` gives `|s| M² ≤ 2 Σ (f² + g²)`. -/
theorem card_mul_sq_le {s : Finset ℕ} {f g : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hfg : ∀ k ∈ s, M ≤ f k + g k) :
    (s.card : ℝ) * M ^ 2 ≤ 2 * ∑ k ∈ s, (f k ^ 2 + g k ^ 2) := by
  rw [Finset.mul_sum, ← nsmul_eq_mul, ← Finset.sum_const]
  apply Finset.sum_le_sum
  intro k hk
  have := hfg k hk
  nlinarith [sq_nonneg (f k - g k)]

/-- CONDITIONAL ON `Inputs`: each window holds at most `K N^{0.8787026}` exceptions. -/
theorem window_count (I : Inputs) : ∃ N2 : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ N, N2 ≤ N →
    ((bad N).card : ℝ) ≤ K * (N : ℝ) ^ θw := by
  obtain ⟨N1, hN1⟩ := main_eventually I
  have hc : c = 0.1215 := rfl
  have hgr : Tendsto (fun x : ℝ => x ^ (0.00005 - η)) atTop atTop :=
    tendsto_rpow_atTop (by unfold η; norm_num)
  obtain ⟨N3, hN3f⟩ := Filter.eventually_atTop.mp
    (tendsto_natCast_atTop_atTop.eventually (hgr.eventually_ge_atTop (2 * (16000000 + |I.C1|))))
  refine ⟨max (max N1 I.N0) (max N3 1), 8 * (|I.C9| + |I.C86|), by positivity, fun N hN => ?_⟩
  have hN1' : N1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN0 : I.N0 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3 : N3 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNpos : 0 < N := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN))
  have hN' : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have rp : ∀ a b : ℝ, (N : ℝ) ^ (a + b) = (N : ℝ) ^ a * (N : ℝ) ^ b := fun a b => rpow_add hN' a b
  have mono : ∀ a b : ℝ, a ≤ b → (N : ℝ) ^ a ≤ (N : ℝ) ^ b :=
    fun a b h => rpow_le_rpow_of_exponent_le hN1r h
  set M : ℝ := (N : ℝ) ^ (1 - η) / 2 with hM
  have hM0 : 0 ≤ M := by positivity
  -- the error terms are at most M
  have herr : 16000000 * (N : ℝ) ^ (0.53 : ℝ) + I.C1 * (N : ℝ) ^ (1 - 0.00005 : ℝ) ≤ M := by
    have h3 := hN3f N hN3
    have hsplit : (N : ℝ) ^ (1 - η) = (N : ℝ) ^ (1 - 0.00005 : ℝ) * (N : ℝ) ^ (0.00005 - η) := by
      rw [← rp]; ring_nf
    have hp := mono 0.53 (1 - 0.00005) (by norm_num)
    have hq : 0 ≤ (N : ℝ) ^ (1 - 0.00005 : ℝ) := by positivity
    have hC1 : I.C1 * (N : ℝ) ^ (1 - 0.00005 : ℝ) ≤ |I.C1| * (N : ℝ) ^ (1 - 0.00005 : ℝ) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hq
    rw [hM, hsplit]
    nlinarith [abs_nonneg I.C1]
  -- every exception in the window has |D₂| + |D₆| ≥ M
  have hfg : ∀ k ∈ bad N, M ≤ ‖I.D2 N k‖ + ‖I.D6 N k‖ := by
    intro k hk
    simp only [bad, Finset.mem_filter, Exc] at hk
    obtain ⟨hkW, h4, hke, hng⟩ := hk
    have hlow := hN1 N hN1' k hkW hke
    have hl1 := I.lemma1 N hN0 k hkW
    have hD := DLu_le_of_not_goldbach N (by omega) hng
    -- k ≤ 2N
    have hk2 : (k : ℝ) ≤ 2 * N := by
      have := rad_le N
      simp only [Win, Finset.mem_Icc] at hkW
      have : k ≤ 2 * N := by omega
      exact_mod_cast this
    have hk53 : (k : ℝ) ^ (0.53 : ℝ) ≤ 2 * (N : ℝ) ^ (0.53 : ℝ) := by
      calc (k : ℝ) ^ (0.53 : ℝ) ≤ (2 * (N : ℝ)) ^ (0.53 : ℝ) :=
            rpow_le_rpow (Nat.cast_nonneg _) hk2 (by norm_num)
        _ = (2 : ℝ) ^ (0.53 : ℝ) * (N : ℝ) ^ (0.53 : ℝ) := mul_rpow (by norm_num) hN'.le
        _ ≤ 2 * (N : ℝ) ^ (0.53 : ℝ) := by
            gcongr
            calc (2 : ℝ) ^ (0.53 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                  rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 2 := rpow_one 2
    -- real part of Lemma 1
    have hre : I.D1 N k + (I.D2 N k).re - DLu N k ≤ I.C1 * (N : ℝ) ^ (1 - 0.00005 : ℝ) := by
      have := Complex.abs_re_le_norm ((DLu N k : ℂ) - ((I.D1 N k : ℂ) + I.D2 N k))
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re] at this
      linarith [neg_abs_le (DLu N k - (I.D1 N k + (I.D2 N k).re))]
    have hre2 : -(I.D2 N k).re ≤ ‖I.D2 N k‖ := by
      have := Complex.abs_re_le_norm (I.D2 N k)
      linarith [neg_abs_le (I.D2 N k).re]
    have hNη : (N : ℝ) ^ (1 - η) = 2 * M := by rw [hM]; ring
    -- DLu ≥ 0 is not needed; combine
    have hD0 : DLu N k ≤ 16000000 * (N : ℝ) ^ (0.53 : ℝ) := by linarith
    linarith
  -- Chebyshev and the two mean squares
  have hcheb := card_mul_sq_le hM0 hfg
  have hsub : ∑ k ∈ bad N, (‖I.D2 N k‖ ^ 2 + ‖I.D6 N k‖ ^ 2) ≤
      ∑ k ∈ Win N, ‖I.D2 N k‖ ^ 2 + ∑ k ∈ Win N, ‖I.D6 N k‖ ^ 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk; simp only [bad, Finset.mem_filter] at hk; exact hk.1
    intro k _ _; positivity
  have h9 := I.sec9 N hN0
  have h86 := I.eq86 N hN0
  -- exponents
  have hE : (N : ℝ) ^ (3.0002 - c) = (N : ℝ) ^ θw * ((N : ℝ) ^ (1 - η)) ^ 2 := by
    rw [← rpow_natCast, ← rpow_mul hN'.le, ← rp]
    unfold θw η; rw [hc]; norm_num
  have h86e : PP N ^ (-1 : ℝ) * dd N * (N : ℝ) ^ (2.0003 : ℝ) = (N : ℝ) ^ (3.0002 - c) := by
    unfold PP dd
    rw [← rpow_mul hN'.le, ← rp, ← rp]; rw [hc]; norm_num
  have h9e : (N : ℝ) ^ (3 - c + 0.00011) ≤ (N : ℝ) ^ (3.0002 - c) := mono _ _ (by linarith)
  have hpos9 : 0 ≤ (N : ℝ) ^ (3 - c + 0.00011) := by positivity
  have hposE : 0 ≤ (N : ℝ) ^ (3.0002 - c) := by positivity
  have hC9 : I.C9 * (N : ℝ) ^ (3 - c + 0.00011) ≤ |I.C9| * (N : ℝ) ^ (3.0002 - c) :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) hpos9).trans
      (mul_le_mul_of_nonneg_left h9e (abs_nonneg _))
  have hC86 : I.C86 * PP N ^ (-1 : ℝ) * dd N * (N : ℝ) ^ (2.0003 : ℝ) ≤
      |I.C86| * (N : ℝ) ^ (3.0002 - c) := by
    rw [mul_assoc, mul_assoc, ← mul_assoc (PP N ^ (-1 : ℝ)), h86e]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) hposE
  have hfin : ((bad N).card : ℝ) * M ^ 2 ≤ 2 * ((|I.C9| + |I.C86|) * (N : ℝ) ^ (3.0002 - c)) := by
    linarith
  -- divide by M² = N^{2-2η}/4
  have hMsq : M ^ 2 = ((N : ℝ) ^ (1 - η)) ^ 2 / 4 := by rw [hM]; ring
  have hQ : 0 < ((N : ℝ) ^ (1 - η)) ^ 2 := by positivity
  rw [hMsq, hE] at hfin
  have : ((bad N).card : ℝ) * ((N : ℝ) ^ (1 - η)) ^ 2 ≤
      (8 * (|I.C9| + |I.C86|) * (N : ℝ) ^ θw) * ((N : ℝ) ^ (1 - η)) ^ 2 := by nlinarith
  exact le_of_mul_le_mul_right this hQ

/-! ### Covering a dyadic block by windows -/

/-- The final exponent, `θw + 0.00021 = 0.8789126`. -/
noncomputable def θ : ℝ := 0.8789126

theorem rad_mono {N N' : ℕ} (hN : 0 < N) (h : N ≤ N') : rad N ≤ rad N' := by
  unfold rad
  rw [rad_eq N hN, rad_eq N' (lt_of_lt_of_le hN h)]
  apply Nat.floor_le_floor
  exact rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast h) (by norm_num)

/-- `rad (Y/2) ≥ Y^{0.99979} / 8` once `Y ≥ 2`. -/
theorem rad_half_ge (Y : ℕ) (hY : 2 ≤ Y) : (Y : ℝ) ^ (0.99979 : ℝ) / 8 ≤ rad (Y / 2) := by
  have hm : 0 < Y / 2 := by omega
  have hm4 : (Y : ℝ) / 4 ≤ ((Y / 2 : ℕ) : ℝ) := by
    have : Y ≤ 2 * (Y / 2) + 1 := by omega
    have h' : (Y : ℝ) ≤ 2 * ((Y / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast this
    have : (2 : ℝ) ≤ Y := by exact_mod_cast hY
    linarith
  unfold rad
  rw [rad_eq _ hm]
  set x := ((Y / 2 : ℕ) : ℝ) ^ (0.99979 : ℝ) with hx
  have hx1 : 1 ≤ x := Real.one_le_rpow (by exact_mod_cast hm) (by norm_num)
  have hfl : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
    have h1 := Nat.lt_floor_add_one x
    have h2 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast Nat.one_le_floor_iff x |>.mpr hx1
    linarith
  have hY0 : (0 : ℝ) ≤ Y := Nat.cast_nonneg _
  have hpow : (Y : ℝ) ^ (0.99979 : ℝ) / 4 ≤ x := by
    calc (Y : ℝ) ^ (0.99979 : ℝ) / 4 ≤ (Y : ℝ) ^ (0.99979 : ℝ) / (4 : ℝ) ^ (0.99979 : ℝ) := by
          gcongr
          calc (4 : ℝ) ^ (0.99979 : ℝ) ≤ (4 : ℝ) ^ (1 : ℝ) :=
                rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 4 := rpow_one 4
      _ = ((Y : ℝ) / 4) ^ (0.99979 : ℝ) := (div_rpow hY0 (by norm_num) _).symm
      _ ≤ x := rpow_le_rpow (by positivity) hm4 (by norm_num)
  linarith

/-- CONDITIONAL ON `Inputs`: the dyadic block `(Y/2, Y]` holds at most `C Y^{0.8789126}`
exceptions for every large `Y`. -/
theorem block_count (I : Inputs) : ∃ C : ℝ, 0 ≤ C ∧ ∃ Y0 : ℕ, ∀ Y : ℕ, Y0 < Y →
    (D Exc Y : ℝ) ≤ C * (Y : ℝ) ^ θ := by
  classical
  obtain ⟨N2, K, hK, hwin⟩ := window_count I
  refine ⟨18 * K, by positivity, 2 * N2 + 4, fun Y hY => ?_⟩
  have hY2 : 2 ≤ Y := by omega
  have hm : 0 < Y / 2 := by omega
  have hmN2 : N2 ≤ Y / 2 := by omega
  set r := rad (Y / 2) with hr
  have hr1 : 1 ≤ r := by
    -- r ≥ 1, the floor of a number ≥ 1
    unfold r rad
    rw [rad_eq _ hm]
    exact Nat.one_le_floor_iff _ |>.mpr (Real.one_le_rpow (by exact_mod_cast hm) (by norm_num))
  have hr0 : 0 < r := hr1
  -- the cover
  have hsub : (Finset.Ioc (Y / 2) Y).filter Exc ⊆
      (Finset.range (Y / r + 1)).biUnion (fun j => bad (Y / 2 + j * r)) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hk
    obtain ⟨⟨hk1, hk2⟩, hex⟩ := hk
    simp only [Finset.mem_biUnion, Finset.mem_range]
    refine ⟨(k - Y / 2) / r, ?_, ?_⟩
    · have : (k - Y / 2) / r ≤ Y / r := Nat.div_le_div_right (by omega)
      omega
    · have hdm := Nat.div_add_mod (k - Y / 2) r
      have hmod := Nat.mod_lt (k - Y / 2) hr0
      have hrad : r ≤ rad (Y / 2 + (k - Y / 2) / r * r) := rad_mono hm (by omega)
      simp only [bad, Finset.mem_filter, Win, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, hex⟩
      · have : (k - Y / 2) / r * r = r * ((k - Y / 2) / r) := Nat.mul_comm _ _
        omega
      · have : (k - Y / 2) / r * r = r * ((k - Y / 2) / r) := Nat.mul_comm _ _
        omega
  have hD : (D Exc Y : ℝ) ≤ ∑ j ∈ Finset.range (Y / r + 1), ((bad (Y / 2 + j * r)).card : ℝ) := by
    have h1 : D Exc Y ≤ ∑ j ∈ Finset.range (Y / r + 1), (bad (Y / 2 + j * r)).card := by
      unfold D
      exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    exact_mod_cast h1
  have hY' : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  have hY1 : (1 : ℝ) ≤ Y := by exact_mod_cast (show 1 ≤ Y by omega)
  -- each window term ≤ 2 K Y^{θw}
  have hterm : ∀ j ∈ Finset.range (Y / r + 1),
      ((bad (Y / 2 + j * r)).card : ℝ) ≤ 2 * K * (Y : ℝ) ^ θw := by
    intro j hj
    simp only [Finset.mem_range] at hj
    have hjr : j * r ≤ Y := by
      have : j ≤ Y / r := by omega
      calc j * r ≤ Y / r * r := Nat.mul_le_mul_right _ this
        _ ≤ Y := Nat.div_mul_le_self Y r
    have hNj : Y / 2 + j * r ≤ 2 * Y := by omega
    have h := hwin (Y / 2 + j * r) (by omega)
    have hNr : ((Y / 2 + j * r : ℕ) : ℝ) ≤ 2 * Y := by exact_mod_cast hNj
    have hθ0 : (0 : ℝ) ≤ θw := by unfold θw; norm_num
    calc ((bad (Y / 2 + j * r)).card : ℝ) ≤ K * ((Y / 2 + j * r : ℕ) : ℝ) ^ θw := h
      _ ≤ K * (2 * (Y : ℝ)) ^ θw := by
          gcongr
      _ = K * ((2 : ℝ) ^ θw * (Y : ℝ) ^ θw) := by rw [mul_rpow (by norm_num) hY'.le]
      _ ≤ K * (2 * (Y : ℝ) ^ θw) := by
          gcongr
          calc (2 : ℝ) ^ θw ≤ (2 : ℝ) ^ (1 : ℝ) :=
                rpow_le_rpow_of_exponent_le (by norm_num) (by unfold θw; norm_num)
            _ = 2 := rpow_one 2
      _ = 2 * K * (Y : ℝ) ^ θw := by ring
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  -- the number of windows
  have hcnt : ((Y / r + 1 : ℕ) : ℝ) ≤ 9 * (Y : ℝ) ^ (0.00021 : ℝ) := by
    have hrr := rad_half_ge Y hY2
    rw [← hr] at hrr
    have hq : ((Y / r : ℕ) : ℝ) ≤ (Y : ℝ) / r := Nat.cast_div_le
    have hP : 0 < (Y : ℝ) ^ (0.99979 : ℝ) := rpow_pos_of_pos hY' _
    have hsplit : (Y : ℝ) = (Y : ℝ) ^ (0.99979 : ℝ) * (Y : ℝ) ^ (0.00021 : ℝ) := by
      rw [← rpow_add hY']; norm_num
    have hrpos : (0 : ℝ) < r := by exact_mod_cast hr0
    have hYr : (Y : ℝ) / r ≤ 8 * (Y : ℝ) ^ (0.00021 : ℝ) := by
      rw [div_le_iff₀ hrpos]
      calc (Y : ℝ) = (Y : ℝ) ^ (0.99979 : ℝ) * (Y : ℝ) ^ (0.00021 : ℝ) := hsplit
        _ ≤ (8 * r) * (Y : ℝ) ^ (0.00021 : ℝ) := by
            gcongr; linarith
        _ = 8 * (Y : ℝ) ^ (0.00021 : ℝ) * r := by ring
    have h1 : (1 : ℝ) ≤ (Y : ℝ) ^ (0.00021 : ℝ) := Real.one_le_rpow hY1 (by norm_num)
    push_cast
    linarith
  have hθ : (Y : ℝ) ^ (0.00021 : ℝ) * (Y : ℝ) ^ θw = (Y : ℝ) ^ θ := by
    rw [← rpow_add hY']; unfold θw θ; norm_num
  have hYθ : 0 ≤ (Y : ℝ) ^ θw := by positivity
  calc (D Exc Y : ℝ) ≤ _ := hD
    _ ≤ ((Y / r + 1 : ℕ) : ℝ) * (2 * K * (Y : ℝ) ^ θw) := by exact_mod_cast hsum
    _ ≤ (9 * (Y : ℝ) ^ (0.00021 : ℝ)) * (2 * K * (Y : ℝ) ^ θw) := by
        gcongr
    _ = 18 * K * ((Y : ℝ) ^ (0.00021 : ℝ) * (Y : ℝ) ^ θw) := by ring
    _ = 18 * K * (Y : ℝ) ^ θ := by rw [hθ]

/-! ### Lu's Theorem, CONDITIONAL ON `Inputs` -/

/-- CONDITIONAL ON `Inputs`: `E X ≪ X^{0.8789126}`, what the combination actually gives. -/
theorem lu_sharp_of_inputs (I : Inputs) : PowerBound θ := by
  obtain ⟨C, hC, Y0, hY⟩ := block_count I
  exact Li2000.powerBound_of_blocks (by unfold θ; norm_num) hC hY

/-- CONDITIONAL ON `Inputs`: the paper's Theorem as printed, `E(x) ≪ x^{0.879}`, the lab's
cited `lu`. -/
theorem lu_of_inputs (I : Inputs) : PowerBound 0.879 :=
  powerBound_of_eventuallyBelow (by norm_num)
    (eventuallyBelow_of_powerBound (by unfold θ; norm_num) (lu_sharp_of_inputs I))

/-- CONDITIONAL ON `Inputs`: the eventual form `E X < X^{0.879}` for all large `X`, as Pintz
2018 eq (1.8) reports Lu, with no constant. -/
theorem lu_eventually_of_inputs (I : Inputs) : Lu2010.lu_eventually_stmt :=
  eventuallyBelow_of_powerBound (by unfold θ; norm_num) (lu_sharp_of_inputs I)

/-! ### The bookkeeping, PROVED -/

/-- The exponents: `η > c·10^{-5}`; per window `max(1.00011 - c, 1.0002 - c) + 2η = θw`;
covering adds `1 - 0.99979`; `θ < 0.879` with margin `8.74·10^{-5}`. -/
theorem exponent_bookkeeping :
    c * 0.00001 < η ∧ 3 - c + 0.00011 - 2 ≤ 0.9999 + 2.0003 - c - 2 ∧
    0.9999 + 2.0003 - c - 2 + 2 * η = θw ∧ θw + (1 - 0.99979) = θ ∧
    θ < 0.879 ∧ (0.879 : ℝ) - θ = 0.0000874 := by
  unfold c η θw θ; norm_num

/-- With `c = 0.121` the same count gives `0.8794126 > 0.879`: the printed exponent needs
the fourth digit of `c = 0.1215`. -/
theorem c_fourth_digit_needed :
    (0.9999 + 2.0003 - 0.121 - 2 + 2 * η + (1 - 0.99979) : ℝ) = 0.8794126 ∧
    (0.879 : ℝ) < 0.8794126 := by
  unfold η; norm_num

/-- Vacuity test: the conclusion is not the trivial bound, it forces `E X < X` eventually. -/
theorem vacuity_forces_lt (I : Inputs) : ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X → (E X : ℝ) < X :=
  Lu2010.lu_eventually_forces_lt (lu_eventually_of_inputs I)

end LeanLab.ExceptionalSet.Lu2010Assembly

#print axioms LeanLab.ExceptionalSet.Lu2010Assembly.rad_eq
#print axioms LeanLab.ExceptionalSet.Lu2010Assembly.bad_mul
#print axioms LeanLab.ExceptionalSet.Lu2010Assembly.DLu_le_RΛ
#print axioms LeanLab.ExceptionalSet.Lu2010Assembly.DLu_le_of_not_goldbach
#print axioms LeanLab.ExceptionalSet.Lu2010Assembly.bracket84_eventually
#print axioms LeanLab.ExceptionalSet.Lu2010Assembly.bracket85_eventually
#print axioms LeanLab.ExceptionalSet.Lu2010Assembly.main_eventually
#print axioms LeanLab.ExceptionalSet.Lu2010Assembly.rad_le
#print axioms LeanLab.ExceptionalSet.Lu2010Assembly.card_mul_sq_le
#print axioms LeanLab.ExceptionalSet.Lu2010Assembly.window_count
#print axioms LeanLab.ExceptionalSet.Lu2010Assembly.rad_mono
#print axioms LeanLab.ExceptionalSet.Lu2010Assembly.rad_half_ge
#print axioms LeanLab.ExceptionalSet.Lu2010Assembly.block_count
#print axioms LeanLab.ExceptionalSet.Lu2010Assembly.lu_sharp_of_inputs
#print axioms LeanLab.ExceptionalSet.Lu2010Assembly.lu_of_inputs
#print axioms LeanLab.ExceptionalSet.Lu2010Assembly.lu_eventually_of_inputs
#print axioms LeanLab.ExceptionalSet.Lu2010Assembly.exponent_bookkeeping
#print axioms LeanLab.ExceptionalSet.Lu2010Assembly.c_fourth_digit_needed
#print axioms LeanLab.ExceptionalSet.Lu2010Assembly.vacuity_forces_lt
