/-
FALSE_core_single_residue_square_mean1622. AI wrote the Lean code. Binary Goldbach is open.

FALSE: two leaves of this folder state false conclusions, and this file refutes both
without any hypothesis.

Leaf one is local_arc_shoulder1622_core_single_residue_square_mean in
SPLIT_local_arc_shoulder1622_core_sum_mean_value.lean. Leaf two is
local_arc_core_unit_mean_value1622 in SPLIT_local_arc_core_unit_integral1622.lean.
Neither leaf file is imported here; each conclusion is copied verbatim as a negated Prop.

Witness regime: modulus 2 and residue 1 for leaf one, the origin for leaf two, and N
large. On the window of half width 1 over 8 M about the centre, with M about 2 N log N,
the damped prime series has modulus at least a constant times N over log N, by the
elementary phase bound and the Chebyshev lower bound pi_ge of Mathlib. The window lies
inside the core interval of half width 1 over N, so the core square mean is at least a
constant times N over log cubed N, while leaf one allows about N to the 13 over 14
times log to the 13 and leaf two allows about N to the 6 over 7 times log to the 13.
No prime number theorem, no GRH and no Mellin input is used.
-/
import LeanLab.Linnik1951.Audit1622

namespace LeanLab.Linnik1951.FALSEcore1622

open MeasureTheory Filter Asymptotics LeanLab.Linnik1951 LeanLab.Linnik1951.Audit1622
open scoped Topology

/-- The lower bound for the prime series on a window about the origin. Every prime up
to M has cosine at least one half, and the tail beyond M is absorbed by the geometric
series. -/
theorem zero_arc_lower (N : ℕ) (hN : 1 ≤ N) (L M : ℕ) (hM : M = 2 * N * L)
    (hL : (N : ℝ) * Real.exp (-(L : ℝ)) ≤ 1) (z : ℝ)
    (hz : |z| ≤ 1 / (8 * (M : ℝ))) (hMpos : 0 < M) :
    ((Nat.primeCounting N : ℝ) - 1) * (Real.exp (-1) / 2) - 9 ≤
      ‖primeFourier111 N z‖ := by
  classical
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hMp : (0 : ℝ) < M := by exact_mod_cast hMpos
  set c : ℕ → ℝ := fun n => Real.exp (-(n : ℝ) / N) with hc
  have hcpos : ∀ n, 0 < c n := fun n => Real.exp_pos _
  let G : ℕ → ℝ := fun n =>
    if n.Prime then c n * Real.cos (2 * Real.pi * z * (n : ℝ)) else 0
  let E : ℕ → ℝ := fun n => Real.exp (-(n : ℝ) / (2 * N))
  let Bd : ℕ → ℝ := fun n => Real.exp (-(L : ℝ)) * E n
  obtain ⟨hEs, hEt⟩ := half_damping_tsum N hN
  have hcs : Summable c := damping_summable111 N hN
  have hGs : Summable G := by
    refine Summable.of_norm_bounded hcs ?_
    intro n
    by_cases hn : n.Prime
    · simp only [G, if_pos hn, norm_mul, Real.norm_eq_abs, abs_of_pos (hcpos n)]
      exact mul_le_of_le_one_right (hcpos n).le (Real.abs_cos_le_one _)
    · simp only [G, if_neg hn, norm_zero]
      exact (hcpos n).le
  have hBs : Summable Bd := hEs.mul_left _
  have hBt : (∑' n, Bd n) ≤ 8 := by
    simp only [Bd]
    rw [tsum_mul_left]
    have := mul_le_mul_of_nonneg_left hEt (Real.exp_pos (-(L : ℝ))).le
    calc _ ≤ Real.exp (-(L : ℝ)) * (8 * (N : ℝ)) := this
      _ = 8 * ((N : ℝ) * Real.exp (-(L : ℝ))) := by ring
      _ ≤ 8 := by linarith
  have hcos : ∀ n : ℕ, n ≤ M → (1 / 2 : ℝ) ≤ Real.cos (2 * Real.pi * z * (n : ℝ)) := by
    intro n hn
    have hnr : (n : ℝ) ≤ M := by exact_mod_cast hn
    have hy : |2 * Real.pi * z * (n : ℝ)| ≤ 1 := by
      have hpi := Real.pi_lt_d2
      have hpi0 := Real.pi_pos
      rw [show 2 * Real.pi * z * (n : ℝ) = (2 * Real.pi * (n : ℝ)) * z by ring, abs_mul,
        abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi * (n : ℝ))]
      calc 2 * Real.pi * (n : ℝ) * |z| ≤ 2 * Real.pi * (M : ℝ) * (1 / (8 * (M : ℝ))) := by
            gcongr
        _ = Real.pi / 4 := by field_simp; ring
        _ ≤ 1 := by linarith
    have h := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * z * (n : ℝ))
    have hsq : (2 * Real.pi * z * (n : ℝ)) ^ 2 ≤ 1 := by
      have := sq_abs (2 * Real.pi * z * (n : ℝ))
      nlinarith [abs_nonneg (2 * Real.pi * z * (n : ℝ))]
    linarith
  have hpr : ∀ n : ℕ, n.Prime → n ≤ M → c n / 2 ≤ G n := by
    intro n hn hnM
    simp only [G, if_pos hn]
    have := hcos n hnM
    nlinarith [hcpos n]
  have hE : ∀ n : ℕ, M < n → c n ≤ Real.exp (-(L : ℝ)) * E n := by
    intro n hn
    have hnr : (M : ℝ) < n := by exact_mod_cast hn
    have hMr : (M : ℝ) = 2 * N * L := by rw [hM]; push_cast; ring
    simp only [c, E]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hd : (L : ℝ) ≤ (n : ℝ) / (2 * N) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have e1 : -(n : ℝ) / N = -((n : ℝ) / (2 * N)) - (n : ℝ) / (2 * N) := by
      field_simp
      ring
    have e2 : -(n : ℝ) / (2 * N) = -((n : ℝ) / (2 * N)) := by ring
    rw [e1, e2]
    linarith
  let s : Finset ℕ := (Finset.range (N + 1)).filter Nat.Prime
  have hNM : N ≤ M := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · subst h0; simp at hM; omega
    · rw [hM]; nlinarith
  have hBd0 : ∀ n, 0 ≤ Bd n := fun n => by simp only [Bd, E]; positivity
  have hnonneg : ∀ n, n ∉ s → 0 ≤ G n + Bd n := by
    intro n _
    by_cases hp : n.Prime
    · by_cases hnM : n ≤ M
      · have := hpr n hp hnM
        have := hcpos n
        have := hBd0 n
        linarith
      · have hlt : M < n := by omega
        have hG : -(c n) ≤ G n := by
          simp only [G, if_pos hp]
          have := Real.neg_one_le_cos (2 * Real.pi * z * (n : ℝ))
          nlinarith [hcpos n]
        have hB : Real.exp (-(L : ℝ)) * E n = Bd n := rfl
        linarith [hE n hlt]
    · simp only [G, if_neg hp, zero_add]
      exact hBd0 n
  have hsum := (hGs.add hBs).sum_le_tsum s hnonneg
  rw [Summable.tsum_add hGs hBs] at hsum
  have hlower : ((s.card : ℝ)) * (Real.exp (-1) / 2) ≤ ∑ n ∈ s, (G n + Bd n) := by
    rw [← nsmul_eq_mul]
    apply Finset.card_nsmul_le_sum
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hnN : n ≤ N := by have := Finset.mem_range.mp hn'.1; omega
    have hg := hpr n hn'.2 (hnN.trans hNM)
    have hce : Real.exp (-1) ≤ c n := by
      simp only [c]
      apply Real.exp_le_exp.mpr
      have hnr : (n : ℝ) ≤ N := by exact_mod_cast hnN
      rw [le_div_iff₀ hNp]
      linarith
    have := hBd0 n
    linarith
  have hcard : (Nat.primeCounting N : ℝ) = s.card := by
    have h2 : Nat.primeCounting N = ((Finset.range (N + 1)).filter Nat.Prime).card := by
      simp only [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
    rw [h2]
  have hre : (primeFourier111 N z).re = ∑' n, G n := by
    have hsS := prime_fourier_summable111 N hN z
    unfold primeFourier111
    rw [Complex.re_tsum hsS]
    have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ)) :=
      Nat.Primes.coe_nat_injective
    have hsupp : Function.support G ⊆ Set.range (fun p : Nat.Primes => (p : ℕ)) := by
      intro n hn
      by_cases hp : n.Prime
      · exact ⟨⟨n, hp⟩, rfl⟩
      · exact absurd (by simp [G, hp] : G n = 0) hn
    rw [← hinj.tsum_eq hsupp]
    apply tsum_congr
    intro p
    simp only [G, if_pos p.2]
    rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  have hnorm : (primeFourier111 N z).re ≤ ‖primeFourier111 N z‖ :=
    (le_abs_self _).trans (Complex.abs_re_le_norm _)
  rw [hre] at hnorm
  have he0 : 0 ≤ Real.exp (-1) / 2 := by positivity
  have hstep : ((Nat.primeCounting N : ℝ) - 1) * (Real.exp (-1) / 2) ≤
      (s.card : ℝ) * (Real.exp (-1) / 2) := by
    rw [← hcard]
    nlinarith
  linarith

/-- The window lower bound at a centre x0, as a Prop shared by the two refutations. -/
def WindowLower (x0 : ℝ) : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∀ L M : ℕ, M = 2 * N * L → (N : ℝ) * Real.exp (-(L : ℝ)) ≤ 1 →
    ∀ z : ℝ, |z| ≤ 1 / (8 * (M : ℝ)) → 0 < M →
      ((Nat.primeCounting N : ℝ) - 1) * (Real.exp (-1) / 2) - 9 ≤
        ‖primeFourier111 N (x0 + z)‖

/-- The window lower bound holds about one half, by half_arc_lower of Audit1622. -/
theorem windowLower_half : WindowLower (1 / 2) :=
  fun N hN L M hM hL z hz hMpos => half_arc_lower N hN L M hM hL z hz hMpos

/-- The window lower bound holds about the origin, by zero_arc_lower. -/
theorem windowLower_zero : WindowLower 0 := by
  intro N hN L M hM hL z hz hMpos
  rw [zero_add]
  exact zero_arc_lower N hN L M hM hL z hz hMpos

/-- For large N the core square mean about a centre with the window lower bound is at
least N over 13824 log cubed N. -/
theorem core_mass (x0 : ℝ) (hw : WindowLower x0) :
    ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log N ∧
      (N : ℝ) / (13824 * Real.log N ^ 3) ≤
        ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), ‖primeFourier111 N (x0 + z)‖ ^ 2 := by
  filter_upwards [eventual_facts 1 one_pos] with N hfacts
  obtain ⟨hl1, hl240, _, hlogs, _⟩ := hfacts
  refine ⟨hl1, ?_⟩
  set ℓ := Real.log N with hℓ
  have hNgt : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp [hℓ] at hl1; linarith
    · exact h
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNgt
  have hN1 : 1 ≤ N := hNgt
  have hℓ0 : 0 < ℓ := by linarith
  have hNbig : 240 ≤ (N : ℝ) := by nlinarith
  set L := Nat.log 2 N + 1 with hLdef
  set M := 2 * N * L with hMdef
  have hLpos : 0 < L := by omega
  have hMpos : 0 < M := by positivity
  have hLe : (N : ℝ) * Real.exp (-(L : ℝ)) ≤ 1 := by
    have h2 : N < 2 ^ L := Nat.lt_pow_succ_log_self (by norm_num) N
    have h2r : (N : ℝ) < 2 ^ L := by exact_mod_cast h2
    have he : (2 : ℝ) ^ L ≤ Real.exp L := by
      rw [show (L : ℝ) = (L : ℝ) * 1 by ring, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)]) L
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
    linarith
  have hLle : (L : ℝ) ≤ 3 * ℓ := by
    have h1 : (2 : ℝ) ^ (Nat.log 2 N) ≤ N := by
      exact_mod_cast Nat.pow_log_le_self 2 hNgt.ne'
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_pow] at h2
    have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have hk : ((Nat.log 2 N : ℕ) : ℝ) ≤ 2 * ℓ := by
      have h0 : (0 : ℝ) ≤ (Nat.log 2 N : ℕ) := Nat.cast_nonneg _
      nlinarith
    simp only [hLdef]
    push_cast
    linarith
  have hMr : (M : ℝ) = 2 * N * L := by simp only [hMdef]; push_cast; ring
  have hMle : (M : ℝ) ≤ 6 * N * ℓ := by rw [hMr]; nlinarith
  set δ : ℝ := 1 / (8 * (M : ℝ)) with hδ
  have hMrpos : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hδpos : 0 < δ := by positivity
  have hpi : (N : ℝ) / (2 * ℓ) ≤ Nat.primeCounting N := by
    have h := Chebyshev.pi_ge N
    refine le_trans ?_ h
    apply (div_le_div_iff₀ (by positivity) hℓ0).mpr
    have hl2 : (0.69 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have : (N : ℝ) * (1 / 2) ≤ (N : ℝ) * Real.log 2 - Real.log ((N : ℝ) + 1) := by
      nlinarith
    nlinarith
  have hX : (N : ℝ) / (24 * ℓ) ≤ ((Nat.primeCounting N : ℝ) - 1) * (Real.exp (-1) / 2) - 9 := by
    have he : (1 / 3 : ℝ) ≤ Real.exp (-1) := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le (Real.exp_pos 1) (Real.exp_one_lt_d9.le.trans (by norm_num))
    have hq : (10 : ℝ) ≤ (N : ℝ) / (24 * ℓ) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hhalf : (N : ℝ) / (2 * ℓ) = 12 * ((N : ℝ) / (24 * ℓ)) := by
      field_simp
      ring
    have hpi2 : 12 * ((N : ℝ) / (24 * ℓ)) ≤ Nat.primeCounting N := by rw [← hhalf]; exact hpi
    set Y := (N : ℝ) / (24 * ℓ)
    have h1 : 0 ≤ (Nat.primeCounting N : ℝ) - 1 := by linarith
    have h2 : ((Nat.primeCounting N : ℝ) - 1) * (1 / 6) ≤
        ((Nat.primeCounting N : ℝ) - 1) * (Real.exp (-1) / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) h1
    linarith
  set Y := (N : ℝ) / (24 * ℓ) with hY
  have hYpos : 0 < Y := by positivity
  have hpoint : ∀ z ∈ Set.Icc (-δ) δ, Y ^ 2 ≤ ‖primeFourier111 N (x0 + z)‖ ^ 2 := by
    intro z hz
    have hz' : |z| ≤ 1 / (8 * (M : ℝ)) := abs_le.mpr ⟨hz.1, hz.2⟩
    have h := hw N hN1 L M rfl hLe z hz' hMpos
    exact pow_le_pow_left₀ hYpos.le (hX.trans h) 2
  have hNM : (N : ℝ) < 8 * (M : ℝ) := by
    rw [hMr]
    have h1L : (1 : ℝ) ≤ L := by exact_mod_cast hLpos
    nlinarith
  have hδN : δ < 1 / (N : ℝ) := one_div_lt_one_div_of_lt hNr hNM
  have hcont : Continuous (fun z : ℝ => ‖primeFourier111 N (x0 + z)‖ ^ 2) :=
    ((continuous_prime_fourier111 N hN1).comp (continuous_const.add continuous_id)).norm.pow 2
  have hle : -(1 / (N : ℝ)) ≤ 1 / (N : ℝ) := by
    have : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
    linarith
  rw [intervalIntegral.integral_of_le hle]
  have hsub : Set.Icc (-δ) δ ⊆ Set.Ioc (-(1 / (N : ℝ))) (1 / (N : ℝ)) := by
    intro z hz
    exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hmono : (∫ z in Set.Icc (-δ) δ, ‖primeFourier111 N (x0 + z)‖ ^ 2) ≤
      ∫ z in Set.Ioc (-(1 / (N : ℝ))) (1 / (N : ℝ)), ‖primeFourier111 N (x0 + z)‖ ^ 2 :=
    setIntegral_mono_set (hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
      (ae_of_all _ fun z => by positivity) (ae_of_all _ fun x hx => hsub hx)
  have hconst := setIntegral_ge_of_const_le_real (μ := volume) (measurableSet_Icc)
    (by simp [Real.volume_Icc] : volume (Set.Icc (-δ) δ) ≠ ⊤)
    hpoint hcont.integrableOn_Icc
  have hvol : volume.real (Set.Icc (-δ) δ) = 2 * δ := by
    rw [Real.volume_real_Icc_of_le (by linarith)]
    ring
  rw [hvol] at hconst
  have hδlow : 1 / (48 * (N : ℝ) * ℓ) ≤ δ := by
    rw [hδ]
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have hlow : (N : ℝ) / (13824 * ℓ ^ 3) ≤ 2 * δ * Y ^ 2 := by
    have : 2 * (1 / (48 * (N : ℝ) * ℓ)) * Y ^ 2 ≤ 2 * δ * Y ^ 2 := by
      gcongr
    refine le_trans (le_of_eq ?_) this
    rw [hY]
    field_simp
    ring
  linarith

/-- Eventual size facts at the exponent one fourteenth. -/
theorem eventual_facts14 (K : ℝ) (hK : 0 < K) :
    ∀ᶠ N : ℕ in atTop,
      K * Real.log N ^ 16 < (N : ℝ) ^ (1 / 14 : ℝ) ∧ (2 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) ∧
        (1 : ℝ) ≤ (N : ℝ) ^ (1 / 14 : ℝ) := by
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h2 : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp hcast).eventually_ge_atTop 2
  have h3 : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ (N : ℝ) ^ (1 / 14 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 14)).comp hcast).eventually_ge_atTop 1
  have h1 : ∀ᶠ N : ℕ in atTop, K * Real.log N ^ 16 < (N : ℝ) ^ (1 / 14 : ℝ) := by
    have hlo := isLittleO_log_rpow_rpow_atTop (16 : ℝ) (by norm_num : (0 : ℝ) < 1 / 14)
    have hb := hlo.bound (show 0 < 1 / (K + 1) by positivity)
    filter_upwards [hcast.eventually hb, hcast.eventually (eventually_gt_atTop (1 : ℝ))]
      with N hN hN1
    have hl : 0 < Real.log N := Real.log_pos hN1
    have hp : 0 < (N : ℝ) ^ (1 / 14 : ℝ) := by positivity
    have hpow : Real.log N ^ (16 : ℝ) = Real.log N ^ (16 : ℕ) := by
      exact_mod_cast Real.rpow_natCast (Real.log N) 16
    rw [hpow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hp,
      abs_of_pos (by positivity : 0 < Real.log N ^ 16)] at hN
    have hd : 0 < K + 1 := by positivity
    have h6 : (K + 1) * Real.log N ^ 16 ≤ (N : ℝ) ^ (1 / 14 : ℝ) := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hd] at hN
      linarith
    have : 0 < Real.log N ^ 16 := by positivity
    nlinarith
  exact h1.and (h2.and h3) |>.mono fun N h => ⟨h.1, h.2.1, h.2.2⟩

/-- FALSE leaf refuted. The conclusion of local_arc_shoulder1622_core_single_residue_square_mean
fails at modulus 2 and residue 1: the core square mean about one half is at least of
order N over log cubed N, while the leaf bound is of order N to the 13 over 14 times log
to the 13. Unconditional; the leaf file is not imported. -/
theorem not_core_single_residue_square_mean1622 : ¬ (
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ a : ℕ, Nat.Coprime a q →
        ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), ‖primeFourier111 N ((a : ℝ) / q + z)‖ ^ 2 ≤
          c * (N : ℝ) * Real.log N ^ 13 *
              (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) /
            (q : ℝ)) := by
  rintro ⟨c, hc, N0, h⟩
  obtain ⟨N, ⟨⟨hl1, hmass⟩, hN0⟩, hfin, h10, hσ1⟩ :=
    (((core_mass (1 / 2) windowLower_half).and (eventually_gt_atTop N0)).and
      (eventual_facts14 (13824 * c) (by positivity))).exists
  have hq2 : ((2 : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) := by simpa using h10
  have hup := h N hN0 2 (by norm_num) hq2 1 (by norm_num)
  have hA : ((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) = 1 / 2 := by norm_num
  rw [hA] at hup
  have hup' := hmass.trans hup
  set ℓ := Real.log N with hℓ
  set σ := (N : ℝ) ^ (1 / 14 : ℝ) with hσ
  have hNgt : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0; simp [hℓ] at hl1; linarith
    · exact h0
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNgt
  have hℓ0 : 0 < ℓ := by linarith
  have hσpos : 0 < σ := by linarith
  have h7 : (N : ℝ) ^ (1 / 7 : ℝ) = σ ^ 2 := by
    rw [hσ, ← Real.rpow_natCast, ← Real.rpow_mul hNr.le]
    norm_num
  rw [h7] at hup'
  have hs1 : 1 / σ ^ 2 ≤ 1 / σ :=
    one_div_le_one_div_of_le hσpos (by nlinarith)
  have hsq : σ ≤ Real.sqrt (((2 : ℕ) : ℝ) * σ ^ 2) := by
    calc σ = Real.sqrt (σ ^ 2) := (Real.sqrt_sq hσpos.le).symm
      _ ≤ Real.sqrt (((2 : ℕ) : ℝ) * σ ^ 2) := Real.sqrt_le_sqrt (by push_cast; nlinarith)
  have hs2 : 1 / Real.sqrt (((2 : ℕ) : ℝ) * σ ^ 2) ≤ 1 / σ :=
    one_div_le_one_div_of_le hσpos hsq
  have hcoef : 0 ≤ c * (N : ℝ) * ℓ ^ 13 := by positivity
  have hbound : c * (N : ℝ) * ℓ ^ 13 *
      (1 / σ ^ 2 + 1 / Real.sqrt (((2 : ℕ) : ℝ) * σ ^ 2)) / ((2 : ℕ) : ℝ) ≤
      c * (N : ℝ) * ℓ ^ 13 / σ := by
    have := mul_le_mul_of_nonneg_left (add_le_add hs1 hs2) hcoef
    push_cast
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    calc c * (N : ℝ) * ℓ ^ 13 * (1 / σ ^ 2 + 1 / Real.sqrt (2 * σ ^ 2))
        ≤ c * (N : ℝ) * ℓ ^ 13 * (1 / σ + 1 / σ) := by exact_mod_cast this
      _ = c * (N : ℝ) * ℓ ^ 13 / σ * 2 := by ring
  have hmain := hup'.trans hbound
  rw [div_le_div_iff₀ (by positivity) hσpos] at hmain
  have : 13824 * c * ℓ ^ 16 * (N : ℝ) < σ * (N : ℝ) := mul_lt_mul_of_pos_right hfin hNr
  have e : c * (N : ℝ) * ℓ ^ 13 * (13824 * ℓ ^ 3) = 13824 * c * ℓ ^ 16 * (N : ℝ) := by ring
  linarith

/-- FALSE leaf refuted. The conclusion of local_arc_core_unit_mean_value1622 fails: the
core square mean about the origin is at least of order N over log cubed N, while the
leaf bound is of order N to the 6 over 7 times log to the 13. Unconditional; the leaf
file is not imported. -/
theorem not_core_unit_mean_value1622 : ¬ (
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 2 ≤ N →
      (∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), ‖primeFourier111 N z‖ ^ 2) ≤
        c * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ))) := by
  rintro ⟨c, hc, h⟩
  obtain ⟨N, ⟨⟨hl1, hmass⟩, hN2⟩, hfacts⟩ :=
    (((core_mass 0 windowLower_zero).and (eventually_ge_atTop 2)).and
      (eventual_facts (2 * c) (by positivity))).exists
  obtain ⟨_, _, _, _, hfin⟩ := hfacts
  simp only [zero_add] at hmass
  have hup' := hmass.trans (h N hN2)
  set ℓ := Real.log N with hℓ
  set τ := (N : ℝ) ^ (1 / 7 : ℝ) with hτ
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hℓ0 : 0 < ℓ := by linarith
  have hτpos : 0 < τ := by positivity
  have he : c * (N : ℝ) * ℓ ^ 13 * (1 / τ) = c * (N : ℝ) * ℓ ^ 13 / τ := by ring
  rw [he, div_le_div_iff₀ (by positivity) hτpos] at hup'
  have : 6912 * (2 * c) * ℓ ^ 16 * (N : ℝ) < τ * (N : ℝ) := mul_lt_mul_of_pos_right hfin hNr
  have e : c * (N : ℝ) * ℓ ^ 13 * (13824 * ℓ ^ 3) = 6912 * (2 * c) * ℓ ^ 16 * (N : ℝ) := by
    ring
  linarith

end LeanLab.Linnik1951.FALSEcore1622

#print axioms LeanLab.Linnik1951.FALSEcore1622.zero_arc_lower
#print axioms LeanLab.Linnik1951.FALSEcore1622.core_mass
#print axioms LeanLab.Linnik1951.FALSEcore1622.not_core_single_residue_square_mean1622
#print axioms LeanLab.Linnik1951.FALSEcore1622.not_core_unit_mean_value1622
