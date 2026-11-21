/-
Cited wall decision for `U1539.lemma4`, run CLOUD-cited-lemma4, 2026-11-20.
Source: P0082, J. Brüdern and A. Perelli, Goldbach numbers in sparse sequences,
Ann. Inst. Fourier 48 (1998) 353-378, page 359, Lemma 4 and its two line proof.

The paper proves Lemma 4 by taking c = 1/2 in Theorem 2 and applying "the standard argument
of Vinogradov [Vi], chapter 5", with details omitted. That standard argument is the passage
from exponential sum bounds to a discrepancy bound. Its modern textbook form is the
Erdős–Turán inequality, accepted here as the NAMED HYPOTHESIS `ErdosTuranDQ4`.

`lemma4_of_erdosTuran_theorem2` proves the sealed statement `Lemma4` from `ErdosTuranDQ4` and
the sealed cited `Theorem2`, with no sorry: the Fourier cutoff grows like
`exp((κ₁/2)(log N)^{3-2γ})`, so `κ = κ₁/2`. `lemma4_of_erdosTuran_lemma10` then routes
`Theorem2` through `U1539.theorem2_of_all_leaves` from the sealed cited Karacuba `Lemma10`.
CONDITIONAL, never PROVED. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.ExceptionalSet.Decomp547a

namespace LeanLab.ExceptionalSet.DQLemma4

open Real Finset Filter
open scoped Topology
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (Theorem2 Lemma4 Lemma10 eC norm_eC)

/-- NAMED HYPOTHESIS. The Erdős–Turán inequality in count form. P. Erdős and P. Turán,
On a problem in the theory of uniform distribution I, Indag. Math. 10 (1948) 370-378, copy in
Lean Lab/copies/ErdosTuran1948-I.pdf (constants unspecified there); in the explicit form of
L. Kuipers and H. Niederreiter, Uniform Distribution of Sequences, Wiley 1974, chapter 2,
Theorem 2.5, p. 112, display (2.33), copy in Lean Lab/copies/KuipersNiederreiter1974-ch2.pdf.
Constants 6/(m+1) and 4/π checked against the page: MATCH, QUEUE U-1739.
For any finite sequence `x_1, ..., x_M` of reals and any positive integer `m`,
`D_M ≤ 6/(m+1) + (4/π) Σ_{h=1}^m (1/h - 1/(m+1)) |(1/M) Σ_n e(h x_n)|`,
where `D_M` is the supremum over `0 ≤ a < b ≤ 1` of `|#{n : {x_n} ∈ [a, b)}/M - (b - a)|`.
Here it is multiplied by `M`, the sequence is indexed by a finite set `s`, and `a = b` is
allowed, which is trivial. This is the "standard argument of Vinogradov" that P0082 page 359
cites from [Vi], chapter 5, in its modern form. -/
def ErdosTuranDQ4 : Prop :=
  ∀ (s : Finset ℕ) (f : ℕ → ℝ) (a b : ℝ), 0 ≤ a → a ≤ b → b ≤ 1 → ∀ m : ℕ, 1 ≤ m →
    |((s.filter (fun n => a ≤ Int.fract (f n) ∧ Int.fract (f n) < b)).card : ℝ)
        - (b - a) * s.card| ≤
      6 * s.card / ((m : ℝ) + 1) +
        4 / Real.pi * ∑ h ∈ Icc 1 m,
          (1 / (h : ℝ) - 1 / ((m : ℝ) + 1)) * ‖∑ n ∈ s, eC ((h : ℝ) * f n)‖

/-- Small `N`: below a fixed bound the trivial bound is absorbed by a constant.
Same argument as `U1539.leaf_small_N`, repeated to avoid importing the sealed file. -/
theorem small_N_dq4 (γ : ℝ) (hγ2 : γ < 3 / 2) (κ : ℝ) (_hκ : 0 < κ) (N₀ : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ N : ℕ, 1 ≤ N → N ≤ N₀ → ∀ α z₁ z₂ : ℝ, 0 ≤ z₂ → z₂ < z₁ → z₁ ≤ 1 →
        |(((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
            z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ)
          - (z₁ - z₂) * N / 2| ≤ B * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := by
  refine ⟨Real.exp (κ * Real.log (N₀ : ℝ) ^ (3 - 2 * γ)), (Real.exp_pos _).le, ?_⟩
  intro N hN hNN₀ α z₁ z₂ hz₂ hz1 hz₁
  have hp : (0 : ℝ) ≤ 3 - 2 * γ := by linarith
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set S : Finset ℕ := (Finset.Ioc (N / 2) N).filter
    (fun n : ℕ => z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁) with hSdef
  have hcard : (S.card : ℝ) ≤ (N : ℝ) := by
    have h1 : S.card ≤ N := by
      rw [hSdef]
      refine le_trans (Finset.card_filter_le _ _) ?_
      rw [Nat.card_Ioc]
      omega
    exact_mod_cast h1
  have hx0 : 0 ≤ (z₁ - z₂) * (N : ℝ) / 2 := by
    have : 0 ≤ z₁ - z₂ := by linarith
    positivity
  have hxN : (z₁ - z₂) * (N : ℝ) / 2 ≤ (N : ℝ) := by
    have h1 : z₁ - z₂ ≤ 1 := by linarith
    have : (0 : ℝ) ≤ (N : ℝ) / 2 := by positivity
    nlinarith
  have hL0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hLM : Real.log (N : ℝ) ≤ Real.log (N₀ : ℝ) :=
    Real.log_le_log hNR (by exact_mod_cast hNN₀)
  have hpow : Real.log (N : ℝ) ^ (3 - 2 * γ) ≤ Real.log (N₀ : ℝ) ^ (3 - 2 * γ) :=
    Real.rpow_le_rpow hL0 hLM hp
  have hexp : (1 : ℝ) ≤
      Real.exp (κ * Real.log (N₀ : ℝ) ^ (3 - 2 * γ)) *
        Real.exp (-κ * Real.log (N : ℝ) ^ (3 - 2 * γ)) := by
    rw [← Real.exp_add, ← Real.exp_zero]
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  have hmain : |(S.card : ℝ) - (z₁ - z₂) * (N : ℝ) / 2| ≤ (N : ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  calc |(S.card : ℝ) - (z₁ - z₂) * (N : ℝ) / 2|
      ≤ (N : ℝ) * 1 := by simpa using hmain
    _ ≤ (N : ℝ) * (Real.exp (κ * Real.log (N₀ : ℝ) ^ (3 - 2 * γ)) *
          Real.exp (-κ * Real.log (N : ℝ) ^ (3 - 2 * γ))) :=
        mul_le_mul_of_nonneg_left hexp hNR.le
    _ = Real.exp (κ * Real.log (N₀ : ℝ) ^ (3 - 2 * γ)) * (N : ℝ) *
          Real.exp (-κ * Real.log (N : ℝ) ^ (3 - 2 * γ)) := by ring

/-- The regime: eventually `exp(κ (log N)^{3-2γ}) ≤ N` and
`2 exp(κ (log N)^{3-2γ}) ≤ F(N)^C`. Elementary. -/
theorem regime_dq4 (γ κ C : ℝ) (hγ1 : 1 < γ) (hγ2 : γ < 3 / 2) (hκ : 0 < κ) (hC : 0 < C) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      1 ≤ N ∧ Real.exp (κ * Real.log N ^ (3 - 2 * γ)) ≤ N ∧
        2 * Real.exp (κ * Real.log N ^ (3 - 2 * γ)) ≤ F γ N ^ C := by
  set p : ℝ := 3 - 2 * γ with hpdef
  have hp0 : 0 < p := by rw [hpdef]; linarith
  have hp1 : p < 1 := by rw [hpdef]; linarith
  set T : ℝ := max κ ((κ + 1) / C) with hTdef
  have ht : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ (1 - p)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < 1 - p)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hl : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    ((ht.eventually_ge_atTop T).and (hl.eventually_ge_atTop 1))
  refine ⟨max N₁ 1, fun N hN => ?_⟩
  obtain ⟨hT, hL1⟩ := hN₁ N ((le_max_left _ _).trans hN)
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  set L : ℝ := Real.log (N : ℝ) with hLdef
  have hLpos : 0 < L := by linarith
  have hLp1 : 1 ≤ L ^ p := Real.one_le_rpow hL1 hp0.le
  have hsplit1 : L ^ (1 - p) * L ^ p = L := by
    rw [← Real.rpow_add hLpos]; simp
  have hsplitγ : L ^ p * L ^ (γ - p) = L ^ γ := by
    rw [← Real.rpow_add hLpos]; congr 1; ring
  have hγp : L ^ (1 - p) ≤ L ^ (γ - p) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hκT : κ ≤ L ^ (1 - p) := (le_max_left _ _).trans hT
  have hCT : (κ + 1) / C ≤ L ^ (γ - p) := ((le_max_right _ _).trans hT).trans hγp
  have hCT' : κ + 1 ≤ C * L ^ (γ - p) := by
    have := (div_le_iff₀ hC).mp hCT; linarith
  refine ⟨hN1, ?_, ?_⟩
  · -- κ L^p ≤ L
    have h1 : κ * L ^ p ≤ L := by
      calc κ * L ^ p ≤ L ^ (1 - p) * L ^ p :=
            mul_le_mul_of_nonneg_right hκT (by positivity)
        _ = L := hsplit1
    calc Real.exp (κ * L ^ p) ≤ Real.exp L := Real.exp_le_exp.mpr h1
      _ = N := by rw [hLdef, Real.exp_log hNR]
  · have h2 : κ * L ^ p + 1 ≤ C * L ^ γ := by
      calc κ * L ^ p + 1 ≤ (κ + 1) * L ^ p := by nlinarith
        _ ≤ (C * L ^ (γ - p)) * L ^ p :=
            mul_le_mul_of_nonneg_right hCT' (by positivity)
        _ = C * L ^ γ := by rw [← hsplitγ]; ring
    have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hF : F γ N ^ C = Real.exp (C * L ^ γ) := by
      rw [F, ← Real.exp_mul]; congr 1; ring
    rw [hF]
    calc 2 * Real.exp (κ * L ^ p) ≤ Real.exp 1 * Real.exp (κ * L ^ p) :=
          mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
      _ = Real.exp (κ * L ^ p + 1) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (C * L ^ γ) := Real.exp_le_exp.mpr h2

/-- The CONDITIONAL assembly. `Lemma4`, P0082 page 359, exactly as sealed in
`U1539.lemma4`, from the named hypothesis `ErdosTuranDQ4` and the sealed cited `Theorem2`,
page 354, taken with `c = 1/2` as the paper says, through
`Decomp547a.integer_multiple_decay_full`. No sorry. -/
theorem lemma4_of_erdosTuran_theorem2 (hET : ErdosTuranDQ4) (hT : Theorem2) : Lemma4 := by
  intro γ hγ1 hγ2
  set C : ℝ := (γ - 1) / 2 with hCdef
  have hC : 0 < C := by rw [hCdef]; linarith
  obtain ⟨κ₁, B₁, hκ₁, hB₁, hdec⟩ :=
    Decomp547a.integer_multiple_decay_full hT γ hγ1 hγ2 C hC (by rw [hCdef]; linarith)
  set κ : ℝ := κ₁ / 2 with hκdef
  have hκ : 0 < κ := by rw [hκdef]; linarith
  obtain ⟨N₀, hN₀⟩ := regime_dq4 γ κ C hγ1 hγ2 hκ hC
  obtain ⟨B₂, -, hsmall⟩ := small_N_dq4 γ hγ2 κ hκ N₀
  refine ⟨κ, max (7 + 4 * B₁) B₂, hκ, ?_⟩
  intro N hN α hlow hhigh z₁ z₂ hz₂ hz1 hz₁
  set E : ℝ := Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) with hEdef
  have hE : 0 < E := Real.exp_pos _
  have hNR : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rcases le_or_gt N N₀ with hle | hgt
  · calc _ ≤ B₂ * N * E := hsmall N hN hle α z₁ z₂ hz₂ hz1 hz₁
      _ ≤ max (7 + 4 * B₁) B₂ * N * E := by
          refine mul_le_mul_of_nonneg_right ?_ hE.le
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) hNR
  · obtain ⟨-, hexpN, hexpF⟩ := hN₀ N hgt.le
    set G : ℝ := Real.exp (κ * Real.log N ^ (3 - 2 * γ)) with hGdef
    have hGE : G * E = 1 := by
      rw [hGdef, hEdef, ← Real.exp_add]; simp
    have hG : 0 < G := Real.exp_pos _
    have hEE : Real.exp (-κ₁ * Real.log N ^ (3 - 2 * γ)) = E * E := by
      rw [hEdef, ← Real.exp_add]; congr 1; rw [hκdef]; ring
    set H : ℕ := Nat.ceil G with hHdef
    have hH1 : 1 ≤ H := by
      rw [hHdef, Nat.one_le_ceil_iff]; exact hG
    have hHG : (H : ℝ) ≤ 2 * G := by
      have h1 := Nat.ceil_lt_add_one hG.le
      have h2 : (1 : ℝ) ≤ G := Real.one_le_exp (by
        have : 0 ≤ Real.log (N : ℝ) ^ (3 - 2 * γ) :=
          Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast hN)) _
        positivity)
      rw [hHdef]; linarith
    have hHF : (H : ℝ) ≤ F γ N ^ C := hHG.trans hexpF
    have hGH : G ≤ (H : ℝ) + 1 := by
      have := Nat.le_ceil G; rw [hHdef]; linarith
    have hNE : 1 ≤ (N : ℝ) * E := by
      calc (1 : ℝ) = G * E := hGE.symm
        _ ≤ N * E := mul_le_mul_of_nonneg_right hexpN hE.le
    set s : Finset ℕ := Finset.Ioc (N / 2) N with hsdef
    have hscard : (s.card : ℝ) ≤ N := by
      have : s.card ≤ N := by rw [hsdef, Nat.card_Ioc]; omega
      exact_mod_cast this
    have hshalf : |(s.card : ℝ) - N / 2| ≤ 1 / 2 := by
      have hc : s.card = N - N / 2 := by rw [hsdef, Nat.card_Ioc]
      have h2 : 2 * (N - N / 2) = N ∨ 2 * (N - N / 2) = N + 1 := by omega
      rw [hc]
      rcases h2 with h2 | h2
      · have : (2 : ℝ) * ((N - N / 2 : ℕ) : ℝ) = N := by exact_mod_cast h2
        rw [abs_le]; constructor <;> linarith
      · have : (2 : ℝ) * ((N - N / 2 : ℕ) : ℝ) = N + 1 := by exact_mod_cast h2
        rw [abs_le]; constructor <;> linarith
    have het := hET s (fun n => α * F γ n) z₂ z₁ hz₂ hz1.le hz₁ H hH1
    -- the reciprocal cutoff term
    have hfirst : 6 * (s.card : ℝ) / ((H : ℝ) + 1) ≤ 6 * N * E := by
      have hpos : (0 : ℝ) < (H : ℝ) + 1 := by positivity
      rw [div_le_iff₀ hpos]
      calc 6 * (s.card : ℝ) ≤ 6 * N := by linarith
        _ = 6 * N * E * G := by
            have : 6 * (N : ℝ) * E * G = 6 * N * (G * E) := by ring
            rw [this, hGE, mul_one]
        _ ≤ 6 * N * E * ((H : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left hGH (by positivity)
    -- each Fourier term
    have hterm : ∀ h ∈ Icc 1 H,
        (1 / (h : ℝ) - 1 / ((H : ℝ) + 1)) *
            ‖∑ n ∈ s, eC ((h : ℝ) * (α * F γ n))‖ ≤ B₁ * N * (E * E) := by
      intro h hh
      obtain ⟨hh1, hh2⟩ := Finset.mem_Icc.mp hh
      have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh1
      have hhH : (h : ℝ) ≤ H := by exact_mod_cast hh2
      have hcoef0 : 0 ≤ 1 / (h : ℝ) - 1 / ((H : ℝ) + 1) := by
        rw [sub_nonneg]
        exact one_div_le_one_div_of_le (by linarith) (by linarith)
      have hcoef1 : 1 / (h : ℝ) - 1 / ((H : ℝ) + 1) ≤ 1 := by
        have : 1 / (h : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hhR
        have : 0 ≤ 1 / ((H : ℝ) + 1) := by positivity
        linarith
      have hS := hdec N hN α hlow hhigh h hh1 (hhH.trans hHF)
      have hS' : ‖∑ n ∈ s, eC ((h : ℝ) * (α * F γ n))‖ ≤ B₁ * N * (E * E) := by
        rw [← hEE]; simpa only [mul_assoc] using hS
      calc _ ≤ 1 * ‖∑ n ∈ s, eC ((h : ℝ) * (α * F γ n))‖ :=
            mul_le_mul_of_nonneg_right hcoef1 (norm_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact hS'
    have hsum : ∑ h ∈ Icc 1 H, (1 / (h : ℝ) - 1 / ((H : ℝ) + 1)) *
          ‖∑ n ∈ s, eC ((h : ℝ) * (α * F γ n))‖ ≤ 2 * B₁ * N * E := by
      calc _ ≤ ∑ h ∈ Icc 1 H, B₁ * N * (E * E) := Finset.sum_le_sum hterm
        _ = (H : ℝ) * (B₁ * N * (E * E)) := by
            rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
        _ ≤ (2 * G) * (B₁ * N * (E * E)) :=
            mul_le_mul_of_nonneg_right hHG (by positivity)
        _ = 2 * B₁ * N * E * (G * E) := by ring
        _ = 2 * B₁ * N * E := by rw [hGE, mul_one]
    have hsum0 : 0 ≤ ∑ h ∈ Icc 1 H, (1 / (h : ℝ) - 1 / ((H : ℝ) + 1)) *
          ‖∑ n ∈ s, eC ((h : ℝ) * (α * F γ n))‖ := by
      apply Finset.sum_nonneg
      intro h hh
      obtain ⟨hh1, hh2⟩ := Finset.mem_Icc.mp hh
      have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh1
      have hhH : (h : ℝ) ≤ H := by exact_mod_cast hh2
      refine mul_nonneg ?_ (norm_nonneg _)
      rw [sub_nonneg]
      exact one_div_le_one_div_of_le (by linarith) (by linarith)
    have hpi : 4 / Real.pi ≤ 2 := by
      rw [div_le_iff₀ Real.pi_pos]; linarith [Real.pi_gt_three]
    have hsecond : 4 / Real.pi * ∑ h ∈ Icc 1 H, (1 / (h : ℝ) - 1 / ((H : ℝ) + 1)) *
          ‖∑ n ∈ s, eC ((h : ℝ) * (α * F γ n))‖ ≤ 4 * B₁ * N * E := by
      calc _ ≤ 2 * (2 * B₁ * N * E) :=
            mul_le_mul hpi hsum hsum0 (by norm_num)
        _ = _ := by ring
    have hmainterm : |(z₁ - z₂) * (s.card : ℝ) - (z₁ - z₂) * N / 2| ≤ N * E := by
      have hz : 0 ≤ z₁ - z₂ := by linarith
      have hz' : z₁ - z₂ ≤ 1 := by linarith
      have : (z₁ - z₂) * (s.card : ℝ) - (z₁ - z₂) * N / 2 =
          (z₁ - z₂) * ((s.card : ℝ) - N / 2) := by ring
      rw [this, abs_mul, abs_of_nonneg hz]
      calc (z₁ - z₂) * |(s.card : ℝ) - N / 2| ≤ 1 * (1 / 2) :=
            mul_le_mul hz' hshalf (abs_nonneg _) (by norm_num)
        _ ≤ N * E := by linarith
    have hcount := het
    calc _ ≤ _ := abs_sub_le _ ((z₁ - z₂) * (s.card : ℝ)) _
      _ ≤ (6 * N * E + 4 * B₁ * N * E) + N * E := by
          refine add_le_add (hcount.trans (add_le_add hfirst hsecond)) hmainterm
      _ = (7 + 4 * B₁) * N * E := by ring
      _ ≤ max (7 + 4 * B₁) B₂ * N * E := by
          refine mul_le_mul_of_nonneg_right ?_ hE.le
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hNR

/-- Route: `Lemma4` CONDITIONAL ON the named hypothesis `ErdosTuranDQ4` and the sealed cited
Karacuba `Lemma10`, P0082 pages 370 and 371, through `U1539.theorem2_of_all_leaves`. -/
theorem lemma4_of_erdosTuran_lemma10 (hET : ErdosTuranDQ4) (h10 : Lemma10) : Lemma4 :=
  lemma4_of_erdosTuran_theorem2 hET (U1539.theorem2_of_all_leaves h10)

/-- Twin check: the conclusion type is the sealed `Lemma4` itself. -/
theorem lemma4_twin_dq4 : (ErdosTuranDQ4 → Theorem2 → Lemma4) ↔
    (ErdosTuranDQ4 → Theorem2 → U1539.Lemma4) := Iff.rfl

end LeanLab.ExceptionalSet.DQLemma4
