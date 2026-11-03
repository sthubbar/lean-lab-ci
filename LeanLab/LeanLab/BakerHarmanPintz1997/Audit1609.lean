/-
Baker, Harman and Pintz 1997, unit U-1609, audit of the statement repairs in DecompJ381 and
DecompJ883. Every theorem here refutes an OLD statement or shows a NEW hypothesis set can hold.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.DecompJ381
import LeanLab.BakerHarmanPintz1997.DecompJ883
import LeanLab.BakerHarmanPintz1997.Deductions

open scoped Real

namespace LeanLab.BakerHarmanPintz1997.Audit1609
open Finset
attribute [local instance] Classical.propDecidable

/-! ### DecompJ381 -/

/-- The old `lemma10_large_L` is refuted by the CODEX task223 theorem. -/
theorem old_lemma10_large_L_false :
    ¬ (∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      ∀ (A0 B c1 c2 : ℝ) (M N : ℝ → DP) (Ml Nl Ll : ℝ → ℝ) (𝒮 : ℝ → Set Cfg), 0 < c1 → c1 < c2 →
        FamOK (fun x => [M x, N x]) [Ml, Nl] B c1 c2 →
        (∀ x, Ml x * Nl x * Ll x = x) →
        (∀ x, ∀ c ∈ 𝒮 x, c.Std x ∧ (c.q : ℝ) ≤ L x ^ A0 ∧ T0 x ≤ c.T ∧ c.T ≤ T1 ε x ∧
          ∀ e ∈ c.S, e.2 = 1 → c.T / 2 ≤ |e.1| ∧ |e.1| ≤ c.T) →
        (∀ x, ∀ c ∈ 𝒮 x, (c.q : ℝ) * c.T < Ll x) →
        Concl39 (fun x => [M x, N x,
          (⟨fun _ => 1, Finset.Ioo ⌊c1 * Ll x⌋₊ ⌈c2 * Ll x⌉₊⟩ : DP)]) 𝒮) :=
  lemma10_large_L_false

/-- The bare input of p. 24, `‖L‖_∞ ≪ 𝓛^B` with no polar term, fails at `χ₀`: for `x = 16 J^8`,
`L = 4 J^8`, `q = 1` and `t ∈ [J, 2J]`, the long polynomial has norm at least `J^3 / 4`. So the input
as printed cannot be a leaf, and `LongSup` carries the term `L^{1/2}/(1+|t|)`. -/
theorem bare_long_sup_false (B' K : ℝ) :
    ¬ ∀ J : ℕ, 16 ≤ J → ∀ i < J,
      ‖∑ n ∈ Ioo (J ^ 8) (4 * J ^ 8), (n : ℂ) ^ (-(half ((J + i : ℕ) : ℝ)))‖ ≤
        K * L (16 * (J : ℝ) ^ 8) ^ B' := by
  intro h
  have hlo := isLittleO_log_rpow_rpow_atTop B' (show (0 : ℝ) < 1 / 8 by norm_num)
  have hev := (hlo.bound (show (0 : ℝ) < 1 / (|K| + 1) by positivity))
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨J, hJbig⟩ := exists_nat_gt (max 16 (max (|X| + 1) 1))
  have hJ16 : (16 : ℝ) < J := (le_max_left _ _).trans_lt hJbig
  have hJ : 16 ≤ J := by exact_mod_cast hJ16.le
  have hJ0 : (0 : ℝ) < J := by linarith
  have hJ1 : (1 : ℝ) ≤ J := by linarith
  have hJX : |X| + 1 < J := (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hJbig
  have hpow : (J : ℝ) ≤ (J : ℝ) ^ 8 := by
    simpa using pow_le_pow_right₀ hJ1 (show 1 ≤ 8 by omega)
  have hx : X ≤ 16 * (J : ℝ) ^ 8 := by linarith [le_abs_self X]
  have hb := hX _ hx
  have hroot : (16 * (J : ℝ) ^ 8) ^ (1 / 8 : ℝ) ≤ 2 * J := by
    have h16 : (16 : ℝ) ^ (1 / 8 : ℝ) ≤ 2 := by
      calc (16 : ℝ) ^ (1 / 8 : ℝ) ≤ (256 : ℝ) ^ (1 / 8 : ℝ) :=
            Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
        _ = 2 := by
            rw [show (256 : ℝ) = 2 ^ (8 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
            norm_num
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast_mul hJ0.le]
    norm_num
    nlinarith
  have hpos : 0 ≤ (16 * (J : ℝ) ^ 8) ^ (1 / 8 : ℝ) := by positivity
  rw [Real.norm_of_nonneg hpos, Real.norm_eq_abs] at hb
  have hupper := h J hJ 0 (by omega)
  have hlower := LargeL223.principal_sample_lower J hJ (t := ((J + 0 : ℕ) : ℝ))
    (by positivity) (by push_cast; linarith)
  have hK : K * L (16 * (J : ℝ) ^ 8) ^ B' ≤ 2 * J := by
    have h1 : K * L (16 * (J : ℝ) ^ 8) ^ B' ≤ |K| * |L (16 * (J : ℝ) ^ 8) ^ B'| := by
      rw [← abs_mul]
      exact le_abs_self _
    have hdiv : |L (16 * (J : ℝ) ^ 8) ^ B'| ≤ 1 / (|K| + 1) * (2 * J) :=
      (show |L (16 * (J : ℝ) ^ 8) ^ B'| ≤ _ from hb).trans
        (mul_le_mul_of_nonneg_left hroot (by positivity))
    have h2 : |K| * |L (16 * (J : ℝ) ^ 8) ^ B'| ≤ (|K| + 1) * (1 / (|K| + 1) * (2 * J)) :=
      mul_le_mul (by linarith) hdiv (abs_nonneg _) (by positivity)
    have h3 : (|K| + 1) * (1 / (|K| + 1) * (2 * (J : ℝ))) = 2 * J := by
      field_simp
    linarith
  have hcube : 2 * (J : ℝ) < (J : ℝ) ^ 3 / 4 := by nlinarith [sq_nonneg ((J : ℝ) - 16)]
  linarith

/-! ### DecompJ883 -/

/-- The statement of `fgm_combine_remainders` before U-1609. -/
def OldCombine : Prop :=
  ∀ C_FGM K_2 N ε : ℝ, 1 ≤ N → 0 < ε →
    C_FGM * N ^ (-1 / 2 : ℝ) * (K_2 * N ^ (ε / 8)) * (2 * N ^ (1 - ε / 4))
    ≤ 2 * C_FGM * K_2 * N ^ (1 / 2 - min (ε / 8) (1 / 4))

/-- The old form fails at `C_FGM = -1`, `K_2 = 1`, `N = 2`, `ε = 4`. -/
theorem old_fgm_combine_remainders_false : ¬ OldCombine := by
  intro h
  have hh := h (-1) 1 2 4 (by norm_num) (by norm_num)
  have h1 : ((2 : ℝ) ^ (-1 / 2 : ℝ)) * (2 : ℝ) ^ ((4 : ℝ) / 8) = 1 := by
    rw [← Real.rpow_add (by norm_num)]
    norm_num
  have hmin : min ((4 : ℝ) / 8) (1 / 4) = 1 / 4 := by norm_num
  have h0 : (1 : ℝ) - 4 / 4 = 0 := by norm_num
  rw [hmin, h0, Real.rpow_zero] at hh
  have hgt : (1 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / 2 - 1 / 4) :=
    Real.one_lt_rpow (by norm_num) (by norm_num)
  nlinarith

/-- The new hypotheses of `fgm_combine_remainders` can hold. -/
theorem fgm_combine_remainders_instance :
    (0 : ℝ) ≤ 1 ∧ (0 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 2 ∧ (0 : ℝ) < 4 ∧
      (1 : ℝ) * 2 ^ (-1 / 2 : ℝ) * (1 * 2 ^ ((4 : ℝ) / 8)) * (2 * 2 ^ (1 - (4 : ℝ) / 4))
        ≤ 2 * 1 * 1 * 2 ^ (1 / 2 - min ((4 : ℝ) / 8) (1 / 4)) :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num,
    DecompJ883.fgm_combine_remainders 1 1 2 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)⟩

/-- The statement of `fgm_discretization_error` before U-1609. -/
def OldDisc : Prop :=
  ∃ C_disc : ℝ, 0 ≤ C_disc ∧ ∀ N N1 : ℝ, 1 ≤ N → N ≤ N1 → N1 ≤ 2 * N → ∀ t : ℝ,
    ‖∑ n ∈ Ioc ⌊N⌋₊ ⌊N1⌋₊, (n : ℂ) ^ (-(t : ℂ) * Complex.I) * (n : ℂ) ^ (-1 / 2 : ℂ) -
      ∫ y in N..N1, (y : ℂ) ^ (-1 / 2 : ℂ) * (y : ℂ) ^ (-(t : ℂ) * Complex.I)‖
    ≤ C_disc * (N : ℝ) ^ (-1 / 2 : ℝ)

/-- One term of the discrete sum, multiplied by a unit, as a real power times a phase. -/
theorem term_rotated {n N : ℕ} (hn : 0 < n) (hN : 0 < N) (t : ℝ) :
    (Complex.exp (((t * Real.log N : ℝ) : ℂ) * Complex.I) *
        ((n : ℂ) ^ (-(t : ℂ) * Complex.I) * (n : ℂ) ^ (-1 / 2 : ℂ))).re =
      (n : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (t * (Real.log n - Real.log N)) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := (Complex.natCast_log).symm
  have h1 : (n : ℂ) ^ (-(t : ℂ) * Complex.I) =
      Complex.exp ((-(t * Real.log n : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.cpow_def_of_ne_zero hn0, hlog]
    congr 1
    push_cast
    ring
  have h2 : (n : ℂ) ^ (-1 / 2 : ℂ) = (((n : ℝ) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
    push_cast
    rfl
  rw [h1, h2]
  have h3 : Complex.exp (((t * Real.log N : ℝ) : ℂ) * Complex.I) *
      (Complex.exp ((-(t * Real.log n : ℝ) : ℂ) * Complex.I) *
        (((n : ℝ) ^ (-1 / 2 : ℝ) : ℝ) : ℂ)) =
      (((n : ℝ) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
        Complex.exp (((t * (Real.log N - Real.log n) : ℝ) : ℂ) * Complex.I) := by
    rw [mul_comm (Complex.exp ((-(t * Real.log n : ℝ) : ℂ) * Complex.I)),
      mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [h3, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  congr 1
  rw [← Real.cos_neg]
  congr 1
  ring

/-- The phase at `t = 2πN` stays near a multiple of `2π` for `k ≤ K`, `N = 16 K²`. -/
theorem phase_cos_lower {K k : ℕ} (hK : 0 < K) (hk : k ≤ K) (hk0 : 0 < k) :
    (1 / 2 : ℝ) ≤ Real.cos (2 * π * ((16 * K ^ 2 : ℕ) : ℝ) *
      (Real.log ((16 * K ^ 2 + k : ℕ) : ℝ) - Real.log ((16 * K ^ 2 : ℕ) : ℝ))) := by
  set N : ℝ := ((16 * K ^ 2 : ℕ) : ℝ) with hNdef
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hN : N = 16 * (K : ℝ) ^ 2 := by rw [hNdef]; push_cast; ring
  have hN0 : 0 < N := by rw [hN]; positivity
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk0
  have hkK : (k : ℝ) ≤ K := by exact_mod_cast hk
  have hcast : ((16 * K ^ 2 + k : ℕ) : ℝ) = N + k := by rw [hN]; push_cast; ring
  rw [hcast, ← Real.log_div (by positivity) hN0.ne']
  set r : ℝ := (N + k) / N with hr
  have hr0 : 0 < r := by positivity
  have hup : Real.log r ≤ r - 1 := Real.log_le_sub_one_of_pos hr0
  have hlo : 1 - r⁻¹ ≤ Real.log r := Real.one_sub_inv_le_log_of_pos hr0
  have hr1 : r - 1 = k / N := by rw [hr]; field_simp; ring
  have hrinv : 1 - r⁻¹ = k / (N + k) := by rw [hr, inv_div]; field_simp; ring
  rw [hr1] at hup
  rw [hrinv] at hlo
  have hhi : N * Real.log r ≤ k := by
    calc N * Real.log r ≤ N * (k / N) := mul_le_mul_of_nonneg_left hup hN0.le
      _ = k := by field_simp
  have hlow : (k : ℝ) - k ^ 2 / N ≤ N * Real.log r := by
    have hdiff : N * (k / (N + k)) - ((k : ℝ) - k ^ 2 / N) = k ^ 3 / (N * (N + k)) := by
      field_simp
      ring
    have hnn : 0 ≤ (k : ℝ) ^ 3 / (N * (N + k)) := by positivity
    have hh : (k : ℝ) - k ^ 2 / N ≤ N * (k / (N + k)) := by linarith
    exact hh.trans (mul_le_mul_of_nonneg_left hlo hN0.le)
  have hrat : (k : ℝ) ^ 2 / N ≤ 1 / 16 := by
    rw [div_le_iff₀ hN0, hN]
    nlinarith
  set y : ℝ := N * Real.log r with hy
  have hcos : Real.cos (2 * π * N * Real.log r) = Real.cos (2 * π * (y - k)) := by
    rw [show 2 * π * (y - k) = 2 * π * y - k * (2 * π) by ring, Real.cos_sub_nat_mul_two_pi]
    congr 1
    rw [hy]
    ring
  rw [hcos]
  have hpi := Real.pi_pos
  have hpi4 := Real.pi_le_four
  have hub : 2 * π * (y - k) ≤ 0 := by nlinarith
  have hlb : -(1 / 2 : ℝ) ≤ 2 * π * (y - k) := by nlinarith
  have hsq : (2 * π * (y - k)) ^ 2 ≤ 1 / 4 := by nlinarith
  have hc := Real.one_sub_sq_div_two_le_cos (x := 2 * π * (y - k))
  linarith

/-- The old `fgm_discretization_error` fails at the resonance `t = 2πN`, with `N = 16 K²` and
`N1 = N + K`: the discrete sum has norm at least `1/16`, the integral is `O(1/K)`, and the claimed
bound is `C/(4K)`. So its error does not tend to zero. -/
theorem old_fgm_discretization_error_false : ¬ OldDisc := by
  rintro ⟨C, hC, h⟩
  obtain ⟨K, hKbig⟩ := exists_nat_gt (max 8 (4 * (C + 1)))
  have hK8 : (8 : ℝ) < K := (le_max_left _ _).trans_lt hKbig
  have hKC : 4 * (C + 1) < K := (le_max_right _ _).trans_lt hKbig
  have hK0 : (0 : ℝ) < K := by linarith
  have hKn : 0 < K := by exact_mod_cast hK0
  set N : ℕ := 16 * K ^ 2 with hNdef
  have hNpos : 0 < N := by positivity
  set NR : ℝ := (N : ℝ) with hNR
  have hNRv : NR = (4 * (K : ℝ)) ^ 2 := by rw [hNR, hNdef]; push_cast; ring
  have hNR0 : 0 < NR := by rw [hNRv]; positivity
  have hNR1 : 1 ≤ NR := by rw [hNRv]; nlinarith
  have hsq : Real.sqrt NR = 4 * K := by rw [hNRv, Real.sqrt_sq (by positivity)]
  have hrootp : NR ^ (1 / 2 : ℝ) = 4 * K := by rw [← Real.sqrt_eq_rpow, hsq]
  have hrootn : NR ^ (-1 / 2 : ℝ) = (4 * (K : ℝ))⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hNR0.le, hrootp]
  set t : ℝ := 2 * π * NR with ht
  have htpos : 0 ≤ t := by positivity
  have hN1cast : ((N + K : ℕ) : ℝ) = NR + K := by rw [hNR]; push_cast; ring
  have hle1 : NR ≤ ((N + K : ℕ) : ℝ) := by rw [hN1cast]; linarith
  have hle2 : ((N + K : ℕ) : ℝ) ≤ 2 * NR := by rw [hN1cast, hNRv]; nlinarith
  have hmain := h NR ((N + K : ℕ) : ℝ) hNR1 hle1 hle2 t
  have hI := DecompJ883.fgm_integral_bound NR ((N + K : ℕ) : ℝ) hNR1 hle1 hle2 t
  rw [hNR, Nat.floor_natCast, Nat.floor_natCast, ← hNR, hrootn] at hmain
  rw [hrootp, abs_of_nonneg htpos] at hI
  set S : ℂ := ∑ n ∈ Ioc N (N + K), (n : ℂ) ^ (-(t : ℂ) * Complex.I) * (n : ℂ) ^ (-1 / 2 : ℂ)
    with hSdef
  set J : ℂ := ∫ y in NR..((N + K : ℕ) : ℝ),
    (y : ℂ) ^ (-1 / 2 : ℂ) * (y : ℂ) ^ (-(t : ℂ) * Complex.I) with hJdef
  have hIsmall : ‖J‖ ≤ (4 * (K : ℝ))⁻¹ := by
    refine hI.trans ?_
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hp : 3 < π := Real.pi_gt_three
    have ht96 : 96 * (K : ℝ) ^ 2 ≤ t := by
      rw [ht, hNRv]
      nlinarith [sq_nonneg (K : ℝ)]
    nlinarith
  set w : ℂ := Complex.exp (((t * Real.log N : ℝ) : ℂ) * Complex.I) with hw
  have hwn : ‖w‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hterm : ∀ n ∈ Ioc N (N + K), (16 * (K : ℝ))⁻¹ ≤
      (w * ((n : ℂ) ^ (-(t : ℂ) * Complex.I) * (n : ℂ) ^ (-1 / 2 : ℂ))).re := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := mem_Ioc.mp hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hn1
    have hn0 : 0 < N + k + 1 := by omega
    rw [hw, term_rotated hn0 hNpos t]
    have hc := phase_cos_lower (K := K) (k := k + 1) hKn (by omega) (by omega)
    have hcast : ((16 * K ^ 2 + (k + 1) : ℕ) : ℝ) = ((N + k + 1 : ℕ) : ℝ) := by
      rw [hNdef, add_assoc]
    rw [hcast, ← hNdef, ← hNR] at hc
    have hpow : (8 * (K : ℝ))⁻¹ ≤ ((N + k + 1 : ℕ) : ℝ) ^ (-1 / 2 : ℝ) := by
      rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg (Nat.cast_nonneg _),
        ← Real.sqrt_eq_rpow]
      apply inv_anti₀ (Real.sqrt_pos.mpr (by exact_mod_cast hn0))
      rw [Real.sqrt_le_left (by positivity)]
      have hkK : ((k + 1 : ℕ) : ℝ) ≤ K := by exact_mod_cast (by omega : k + 1 ≤ K)
      have hcast2 : ((N + k + 1 : ℕ) : ℝ) = NR + ((k + 1 : ℕ) : ℝ) := by
        rw [hNR]; push_cast; ring
      rw [hcast2, hNRv]
      nlinarith
    calc (16 * (K : ℝ))⁻¹ = (8 * (K : ℝ))⁻¹ * (1 / 2) := by field_simp; norm_num
      _ ≤ ((N + k + 1 : ℕ) : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (t * (Real.log ((N + k + 1 : ℕ) : ℝ) -
          Real.log (N : ℝ))) :=
        mul_le_mul hpow hc (by norm_num) (by positivity)
  have hSlow : (1 / 16 : ℝ) ≤ ‖S‖ := by
    have hre : (w * S).re = ∑ n ∈ Ioc N (N + K),
        (w * ((n : ℂ) ^ (-(t : ℂ) * Complex.I) * (n : ℂ) ^ (-1 / 2 : ℂ))).re := by
      rw [hSdef, Finset.mul_sum, Complex.re_sum]
    have hsum : (1 / 16 : ℝ) ≤ (w * S).re := by
      rw [hre]
      calc (1 / 16 : ℝ) = ∑ _n ∈ Ioc N (N + K), (16 * (K : ℝ))⁻¹ := by
            rw [sum_const, Nat.card_Ioc, nsmul_eq_mul]
            have : N + K - N = K := by omega
            rw [this]
            field_simp
        _ ≤ _ := sum_le_sum hterm
    calc (1 / 16 : ℝ) ≤ (w * S).re := hsum
      _ ≤ ‖w * S‖ := Complex.re_le_norm _
      _ = ‖S‖ := by rw [norm_mul, hwn, one_mul]
  have htri : ‖S‖ ≤ ‖S - J‖ + ‖J‖ := by
    simpa using norm_add_le (S - J) J
  have hfinal : (1 / 16 : ℝ) ≤ (C + 1) * (4 * (K : ℝ))⁻¹ := by
    have hmain' : ‖S - J‖ ≤ C * (4 * (K : ℝ))⁻¹ := hmain
    nlinarith
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)] at hfinal
  linarith

/-- The nonresonant hypotheses of the new `fgm_discretization_error` hold with a nonempty sum. -/
theorem fgm_discretization_error_instance :
    (1 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 2 ∧ (2 : ℝ) ≤ 2 * 1 ∧ |(1 : ℝ)| ≤ 1 ∧
      (Ioc ⌊(1 : ℝ)⌋₊ ⌊(2 : ℝ)⌋₊).Nonempty := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ⟨2, ?_⟩⟩
  simp

/-! ### A nonempty instance of the repaired Lemma 10 and of the repaired large L leaf

The configurations are the principal samples of `lemma10_large_L_false`, at `x = J^10`, with
`M = N = n^{-s}` a monomial of length `x^{1/10} = J`, so `MN ≍ J²` beats `T₀` and `L = J^8`. -/

/-- The short length. Below `16` it only serves the global quantifier of the hypotheses. -/
noncomputable def vF (ε x : ℝ) : ℝ := if 16 ≤ x then x ^ (1 / 10 : ℝ) else min (-1) (x ^ (0.46 + ε / 8))

/-- The short monomial, empty below `16`. -/
noncomputable def vP (ε x : ℝ) : DP :=
  if 16 ≤ x then ⟨fun _ => 1, {2 * ⌈vF ε x⌉₊}⟩ else ⟨fun _ => 0, ∅⟩

/-- The long length. -/
noncomputable def vLl (ε x : ℝ) : ℝ := x / (vF ε x * vF ε x)

/-- The principal sample configurations. -/
def vS : ℝ → Set Cfg := fun x => {c | ∃ J : ℕ, 16 ≤ J ∧ 16 ≤ Real.log J ∧ x = (J : ℝ) ^ 10 ∧
  c = LargeL223.principalCfg J}

theorem vF_ne (ε x : ℝ) : vF ε x ≠ 0 := by
  by_cases hx : 16 ≤ x
  · simp only [vF, if_pos hx]
    exact (Real.rpow_pos_of_pos (by linarith) _).ne'
  · have hh : vF ε x ≤ -1 := by
      simpa only [vF, if_neg hx] using min_le_left (-1) (x ^ (0.46 + ε / 8))
    linarith

theorem v_prod (ε x : ℝ) : vF ε x * vF ε x * vLl ε x = x := by
  have := vF_ne ε x
  simp only [vLl]
  field_simp

theorem v_fam (ε : ℝ) : FamOK (fun x => [vP ε x, vP ε x]) [vF ε, vF ε] 0 1 4 := by
  intro x
  refine ⟨rfl, ?_⟩
  intro i hi hi'
  have hi01 : i = 0 ∨ i = 1 := by simp at hi; omega
  have key : (vP ε x).HasLen (vF ε x) 1 4 ∧ (vP ε x).Coef31 0 := by
    by_cases hx : 16 ≤ x
    · have hF1 : 1 ≤ vF ε x := by
        simp only [vF, if_pos hx]
        exact Real.one_le_rpow (by linarith) (by norm_num)
      constructor
      · intro n hn
        simp only [vP, if_pos hx, mem_singleton] at hn
        subst n
        have h1 := Nat.le_ceil (vF ε x)
        have h2 := Nat.ceil_lt_add_one (show 0 ≤ vF ε x by linarith)
        push_cast
        constructor <;> linarith
      · intro n hn
        simp [vP, if_pos hx, Real.rpow_zero]
    · constructor
      · intro n hn
        simp [vP, if_neg hx] at hn
      · intro n hn
        simp [vP, if_neg hx] at hn
  rcases hi01 with rfl | rfl <;> simpa using key

theorem v_or {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    max (vF ε x) (x ^ (0.45 : ℝ)) * max (vF ε x) (x ^ (0.225 : ℝ)) ≤ x ^ (0.775 + ε / 8) ∨
      max (vF ε x) (vF ε x) ≤ x ^ (0.46 + ε / 8) := by
  right
  rw [max_self]
  by_cases hx : 16 ≤ x
  · simp only [vF, if_pos hx]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  · simpa only [vF, if_neg hx] using min_le_right (-1) (x ^ (0.46 + ε / 8))

/-- `T₀ ≤ MN`, for `x ≥ exp 12`. -/
theorem v_MN (ε : ℝ) : ∃ X1 : ℝ, ∀ x, X1 ≤ x → T0 x ≤ vF ε x * vF ε x := by
  refine ⟨Real.exp 12, fun x hx => ?_⟩
  have hexp : (16 : ℝ) ≤ Real.exp 12 := by
    have h4 : (4 : ℝ) ≤ Real.exp 3 := by
      have := Real.add_one_le_exp (3 : ℝ)
      linarith
    have h5 : Real.exp 12 = Real.exp 3 ^ 4 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h5]
    calc (16 : ℝ) ≤ 4 ^ 4 := by norm_num
      _ ≤ Real.exp 3 ^ 4 := pow_le_pow_left₀ (by norm_num) h4 4
  have hx16 : 16 ≤ x := hexp.trans hx
  have hx0 : 0 < x := by linarith
  have hL : 12 ≤ L x := by
    have hh := Real.log_le_log (Real.exp_pos 12) hx
    rwa [Real.log_exp] at hh
  simp only [vF, if_pos hx16]
  rw [← Real.rpow_add hx0]
  have hcube : (L x ^ (1 / 3 : ℝ)) ^ 3 ≤ (L x / 5) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
    nlinarith [sq_nonneg (L x)]
  have hle : L x ^ (1 / 3 : ℝ) ≤ L x / 5 :=
    (pow_le_pow_iff_left₀ (by positivity) (by linarith) (by omega : 3 ≠ 0)).mp hcube
  have hrew : x ^ ((1 / 10 : ℝ) + 1 / 10) = Real.exp (L x / 5) := by
    rw [Real.rpow_def_of_pos hx0]
    congr 1
    simp only [L]
    ring
  rw [hrew]
  exact Real.exp_le_exp.mpr hle

theorem v_values {ε : ℝ} {J : ℕ} (hJ : 16 ≤ J) :
    vF ε ((J : ℝ) ^ 10) = J ∧ vLl ε ((J : ℝ) ^ 10) = (J : ℝ) ^ 8 := by
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  have hJ16 : (16 : ℝ) ≤ J := by exact_mod_cast hJ
  have hx : (16 : ℝ) ≤ (J : ℝ) ^ 10 := by
    have := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ J) (show 1 ≤ 10 by omega)
    linarith
  have hF : vF ε ((J : ℝ) ^ 10) = J := by
    simp only [vF, if_pos hx]
    rw [← Real.rpow_natCast_mul hJ0.le]
    norm_num
  refine ⟨hF, ?_⟩
  simp only [vLl, hF]
  field_simp

theorem v_large {ε : ℝ} : ∀ x, ∀ c ∈ vS x, (c.q : ℝ) * c.T < vLl ε x := by
  intro x c hc
  obtain ⟨J, hJ, -, rfl, rfl⟩ := hc
  rw [(v_values hJ).2]
  have hJ16 : (16 : ℝ) ≤ J := by exact_mod_cast hJ
  have hJ1 : (1 : ℝ) ≤ J := by linarith
  have hp : (J : ℝ) ^ 2 ≤ (J : ℝ) ^ 8 := pow_le_pow_right₀ hJ1 (by omega)
  norm_num [LargeL223.principalCfg]
  nlinarith

theorem v_std {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 16) : ∀ x, ∀ c ∈ vS x,
    c.Std x ∧ (c.q : ℝ) ≤ L x ^ (0 : ℝ) ∧ T0 x ≤ c.T ∧ c.T ≤ T1 ε x ∧
      ∀ e ∈ c.S, e.2 = 1 → c.T / 2 ≤ |e.1| ∧ |e.1| ≤ c.T := by
  intro x c hc
  obtain ⟨J, hJ, hlog, rfl, rfl⟩ := hc
  have hJ16 : (16 : ℝ) ≤ J := by exact_mod_cast hJ
  have hJ0 : (0 : ℝ) < J := by linarith
  have hJ1 : (1 : ℝ) ≤ J := by linarith
  have hp : (J : ℝ) ^ 2 ≤ (J : ℝ) ^ 10 := pow_le_pow_right₀ hJ1 (by omega)
  have hx1 : (1 : ℝ) ≤ (J : ℝ) ^ 10 := one_le_pow₀ hJ1
  refine ⟨⟨LargeL223.principalCfg_wellSpaced J, by norm_num [LargeL223.principalCfg], ?_, ?_, ?_⟩,
    by simp [LargeL223.principalCfg], ?_, ?_, LargeL223.principalCfg_heights J⟩
  · norm_num [LargeL223.principalCfg]; linarith
  · dsimp [LargeL223.principalCfg]; linarith
  · norm_num [LargeL223.principalCfg]; nlinarith
  · have hLx : L ((J : ℝ) ^ 10) = 10 * Real.log J := by
      unfold L
      rw [Real.log_pow]
      norm_num
    have hLnn : 0 ≤ L ((J : ℝ) ^ 10) := by rw [hLx]; linarith
    have hcube : (L ((J : ℝ) ^ 10) ^ (1 / 3 : ℝ)) ^ 3 ≤ (Real.log J) ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hLnn]
      norm_num
      rw [hLx]
      nlinarith [sq_nonneg (Real.log J)]
    have hle : L ((J : ℝ) ^ 10) ^ (1 / 3 : ℝ) ≤ Real.log J :=
      (pow_le_pow_iff_left₀ (by positivity) (by linarith) (by omega : 3 ≠ 0)).mp hcube
    have hh := Real.exp_le_exp.mpr hle
    rw [Real.exp_log hJ0] at hh
    dsimp [T0, LargeL223.principalCfg]
    linarith
  · have hr : (((J : ℝ) ^ 10) ^ (1 / 5 : ℝ)) = (J : ℝ) ^ 2 := by
      rw [← Real.rpow_natCast_mul hJ0.le, show ((10 : ℕ) : ℝ) * (1 / 5 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
    have hmono := Real.rpow_le_rpow_of_exponent_le hx1
      (show (1 / 5 : ℝ) ≤ 0.45 - 2 * ε / 3 by linarith)
    rw [hr] at hmono
    dsimp [LargeL223.principalCfg, T1]
    nlinarith

/-- The upper companion of `LargeL223.principal_sum_lower`. -/
theorem principal_sum_upper (k : ℕ) (hk : 0 < k) (t : ℝ) :
    ‖∑ n ∈ Ioo k (4 * k), (n : ℂ) ^ (-(half t))‖ ≤
      9 * (k : ℝ) ^ (1 / 2 : ℝ) / (1 + |t|) + (3 * |t| + 4) * (k : ℝ) ^ (-1 / 2 : ℝ) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hb := LargeL223.sum_integral_error (fun x => (x : ℂ) ^ (-(half t)))
    (fun x => (-(half t)) * (x : ℂ) ^ (-(half t) - 1)) k (4 * k) (by omega)
    (D := (|t| + 1) * (k : ℝ) ^ (-3 / 2 : ℝ)) (by positivity)
    (fun x hx => LargeL223.principal_hasDerivAt t (hk0.trans_le hx.1))
    (fun x hx => LargeL223.principal_derivative_norm t hk0 hx.1)
  have hcount : (4 * k - k : ℕ) = 3 * k := by omega
  rw [hcount] at hb
  have hpower : (k : ℝ) * (k : ℝ) ^ (-3 / 2 : ℝ) = (k : ℝ) ^ (-1 / 2 : ℝ) := by
    nth_rw 1 [← Real.rpow_one (k : ℝ)]
    rw [← Real.rpow_add hk0]
    norm_num
  have herr : ‖(∑ n ∈ Ico k (4 * k), (n : ℂ) ^ (-(half t))) -
      ∫ x in (k : ℝ)..(4 * k), (x : ℂ) ^ (-(half t))‖ ≤
        3 * (|t| + 1) * (k : ℝ) ^ (-1 / 2 : ℝ) := by
    convert hb using 1
    · simp
    · push_cast
      rw [← hpower]
      ring
  have hsplit : (∑ n ∈ Ico k (4 * k), (n : ℂ) ^ (-(half t))) =
      (k : ℂ) ^ (-(half t)) + ∑ n ∈ Ioo k (4 * k), (n : ℂ) ^ (-(half t)) := by
    rw [← Finset.sum_insert (f := fun n : ℕ => (n : ℂ) ^ (-(half t))) (by simp)]
    congr 1
    ext n
    simp only [mem_insert, mem_Ico, mem_Ioo]
    omega
  have hkterm : ‖(k : ℂ) ^ (-(half t))‖ = (k : ℝ) ^ (-1 / 2 : ℝ) := by
    simpa using LargeL223.principal_norm t hk0
  have hint : ‖∫ x in (k : ℝ)..(4 * k), (x : ℂ) ^ (-(half t))‖ ≤
      9 * (k : ℝ) ^ (1 / 2 : ℝ) / (1 + |t|) := by
    have hr : -1 < (-(half t)).re := by norm_num [half]
    rw [integral_cpow (Or.inl hr), norm_div]
    have hre : (-(half t) + 1).re = (1 / 2 : ℝ) := by norm_num [half]
    have hroot : (0 : ℝ) ≤ (k : ℝ) ^ (1 / 2 : ℝ) := by positivity
    have hnum : ‖((4 * k : ℝ) : ℂ) ^ (-(half t) + 1) - (k : ℂ) ^ (-(half t) + 1)‖ ≤
        3 * (k : ℝ) ^ (1 / 2 : ℝ) := by
      have hh := norm_sub_le (((4 * k : ℝ) : ℂ) ^ (-(half t) + 1))
        ((((k : ℝ) : ℂ)) ^ (-(half t) + 1))
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),
        Complex.norm_cpow_eq_rpow_re_of_pos hk0, hre, Real.mul_rpow (by norm_num) hk0.le] at hh
      have hfour : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
        rw [← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]
      rw [hfour] at hh
      have hcast : ((k : ℂ)) = (((k : ℝ)) : ℂ) := by push_cast; rfl
      rw [hcast]
      linarith
    have hd1 : (1 / 2 : ℝ) ≤ ‖-(half t) + 1‖ := by
      have hh := Complex.abs_re_le_norm (-(half t) + 1)
      rw [hre] at hh
      norm_num at hh
      exact hh
    have hd2 : |t| ≤ ‖-(half t) + 1‖ := by
      have hh := Complex.abs_im_le_norm (-(half t) + 1)
      have him : (-(half t) + 1).im = -t := by simp [half]
      rw [him, abs_neg] at hh
      exact hh
    have hd0 : 0 < ‖-(half t) + 1‖ := by linarith
    rw [div_le_div_iff₀ hd0 (by positivity)]
    have hcast4 : ((4 * (k : ℝ) : ℝ) : ℂ) = ((4 * k : ℝ) : ℂ) := rfl
    have hmul : ‖((4 * k : ℝ) : ℂ) ^ (-(half t) + 1) - (k : ℂ) ^ (-(half t) + 1)‖ * (1 + |t|) ≤
        3 * (k : ℝ) ^ (1 / 2 : ℝ) * (3 * ‖-(half t) + 1‖) :=
      mul_le_mul hnum (by linarith) (by positivity) (by positivity)
    have hgoal := hmul
    push_cast at hgoal ⊢
    nlinarith
  have htri : ‖∑ n ∈ Ioo k (4 * k), (n : ℂ) ^ (-(half t))‖ ≤
      ‖(k : ℂ) ^ (-(half t))‖ +
        ‖(∑ n ∈ Ico k (4 * k), (n : ℂ) ^ (-(half t))) -
          ∫ x in (k : ℝ)..(4 * k), (x : ℂ) ^ (-(half t))‖ +
        ‖∫ x in (k : ℝ)..(4 * k), (x : ℂ) ^ (-(half t))‖ := by
    rw [hsplit]
    set A := (k : ℂ) ^ (-(half t))
    set B := ∑ n ∈ Ioo k (4 * k), (n : ℂ) ^ (-(half t))
    set I := ∫ x in (k : ℝ)..(4 * k), (x : ℂ) ^ (-(half t))
    have h : B = -A + ((A + B) - I) + I := by ring
    calc ‖B‖ = ‖-A + ((A + B) - I) + I‖ := by rw [← h]
      _ ≤ ‖-A + ((A + B) - I)‖ + ‖I‖ := norm_add_le _ _
      _ ≤ ‖-A‖ + ‖(A + B) - I‖ + ‖I‖ := by gcongr; exact norm_add_le _ _
      _ = _ := by rw [norm_neg]
  rw [hkterm] at htri
  have hroot : (0 : ℝ) ≤ (k : ℝ) ^ (-1 / 2 : ℝ) := by positivity
  nlinarith [abs_nonneg t]

/-- `LongSup` holds on the instance, with its polar term. Only the polar clause is used, and the
instance is the very family that refutes the bare input. -/
theorem v_longSup (ε : ℝ) : LongSup 1 4 (vLl ε) vS := by
  refine ⟨1, 10, Real.exp 1, ?_⟩
  intro x hx c hc e he
  obtain ⟨J, hJ, hlog, rfl, rfl⟩ := hc
  obtain ⟨i, hi, rfl⟩ := mem_image.mp he
  have hJ16 : (16 : ℝ) ≤ J := by exact_mod_cast hJ
  have hJ0 : (0 : ℝ) < J := by linarith
  have hJ1 : (1 : ℝ) ≤ J := by linarith
  have hiJ : (i : ℝ) < J := by exact_mod_cast mem_range.mp hi
  refine ⟨fun h => absurd rfl h, fun _ => ?_⟩
  have hLl := (v_values (ε := ε) hJ).2
  dsimp only
  rw [hLl, Real.rpow_one]
  have hsupp : (longDP 1 4 ((J : ℝ) ^ 8)).supp = Ioo (J ^ 8) (4 * J ^ 8) := by
    have h1 : (1 : ℝ) * (J : ℝ) ^ 8 = ((J ^ 8 : ℕ) : ℝ) := by push_cast; ring
    have h2 : (4 : ℝ) * (J : ℝ) ^ 8 = ((4 * J ^ 8 : ℕ) : ℝ) := by push_cast; ring
    simp only [longDP]
    rw [h1, h2, Nat.floor_natCast, Nat.ceil_natCast]
  have hχ : ∀ z : ZMod 1, (1 : DirichletCharacter ℂ 1) z = 1 := by
    intro z
    apply MulChar.one_apply
    have hz : z = 1 := Subsingleton.elim _ _
    rw [hz]
    exact isUnit_one
  have heval : (longDP 1 4 ((J : ℝ) ^ 8)).eval (1 : DirichletCharacter ℂ 1)
      (half ((J + i : ℕ) : ℝ)) =
      ∑ n ∈ Ioo (J ^ 8) (4 * J ^ 8), (n : ℂ) ^ (-(half ((J + i : ℕ) : ℝ))) := by
    unfold DP.eval
    rw [hsupp]
    simp [longDP, hχ]
  have hb := principal_sum_upper (J ^ 8) (by positivity) ((J + i : ℕ) : ℝ)
  set t : ℝ := ((J + i : ℕ) : ℝ) with ht
  have ht0 : 0 ≤ t := by positivity
  have ht2 : t ≤ 2 * J := by rw [ht]; push_cast; linarith
  have hkcast : ((J ^ 8 : ℕ) : ℝ) = (J : ℝ) ^ 8 := by push_cast; rfl
  have hrootn : ((J : ℝ) ^ 8) ^ (-1 / 2 : ℝ) = ((J : ℝ) ^ 4)⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg (by positivity),
      ← Real.rpow_natCast_mul hJ0.le]
    norm_num
  rw [hkcast, hrootn, abs_of_nonneg ht0] at hb
  change ‖(longDP 1 4 ((J : ℝ) ^ 8)).eval (1 : DirichletCharacter ℂ 1) (half t)‖ ≤
    10 * (L ((J : ℝ) ^ 10) + ((J : ℝ) ^ 8) ^ (1 / 2 : ℝ) / (1 + |t|))
  rw [heval, abs_of_nonneg ht0]
  have herr : (3 * t + 4) * ((J : ℝ) ^ 4)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one (by positivity)]
    have hp : (J : ℝ) ≤ (J : ℝ) ^ 4 := by
      simpa using pow_le_pow_right₀ hJ1 (show 1 ≤ 4 by omega)
    have hp2 : (J : ℝ) ^ 2 ≤ (J : ℝ) ^ 4 := pow_le_pow_right₀ hJ1 (by omega)
    nlinarith
  have hLge : 1 ≤ L ((J : ℝ) ^ 10) := by
    unfold L
    rw [Real.log_pow]
    push_cast
    linarith
  have hmain : (0 : ℝ) ≤ ((J : ℝ) ^ 8) ^ (1 / 2 : ℝ) / (1 + t) := by positivity
  have hfrac : 9 * ((J : ℝ) ^ 8) ^ (1 / 2 : ℝ) / (1 + t) =
      9 * (((J : ℝ) ^ 8) ^ (1 / 2 : ℝ) / (1 + t)) := by ring
  rw [hfrac] at hb
  linarith

/-- All hypotheses of `Lemma10Repaired` and of the new `lemma10_large_L` hold at once on a family
with nonempty `𝒮` at unbounded `x`, at every small `ε`. It has `A0 = B = 0`, `c1 = 1`, `c2 = 4`. -/
theorem lemma10_repaired_instance {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 16) :
    FamOK (fun x => [vP ε x, vP ε x]) [vF ε, vF ε] 0 1 4 ∧
    (∀ x, vF ε x * vF ε x * vLl ε x = x) ∧
    (∀ x, ∀ c ∈ vS x, c.Std x ∧ (c.q : ℝ) ≤ L x ^ (0 : ℝ) ∧ T0 x ≤ c.T ∧ c.T ≤ T1 ε x ∧
      ∀ e ∈ c.S, e.2 = 1 → c.T / 2 ≤ |e.1| ∧ |e.1| ≤ c.T) ∧
    (∀ x, ∀ c ∈ vS x, (c.q : ℝ) * c.T < vLl ε x) ∧
    (∀ x, max (vF ε x) (x ^ (0.45 : ℝ)) * max (vF ε x) (x ^ (0.225 : ℝ)) ≤ x ^ (0.775 + ε / 8) ∨
      max (vF ε x) (vF ε x) ≤ x ^ (0.46 + ε / 8)) ∧
    (∃ X1 : ℝ, ∀ x, X1 ≤ x → T0 x ≤ vF ε x * vF ε x) ∧
    LongSup 1 4 (vLl ε) vS ∧
    (∀ X : ℝ, ∃ x, X ≤ x ∧ ∃ c ∈ vS x, c.S.Nonempty) := by
  refine ⟨v_fam ε, v_prod ε, v_std hε hε', v_large, v_or hε, v_MN ε, v_longSup ε, ?_⟩
  intro X
  obtain ⟨J, hJbig⟩ := exists_nat_gt (max 16 (max X (Real.exp 16)))
  have hJ16 : (16 : ℝ) < J := (le_max_left _ _).trans_lt hJbig
  have hJX : X < J := (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hJbig
  have hJe : Real.exp 16 < J := (le_trans (le_max_right _ _) (le_max_right _ _)).trans_lt hJbig
  have hJ : 16 ≤ J := by exact_mod_cast hJ16.le
  have hlog : 16 ≤ Real.log J := by
    have hh := Real.log_lt_log (Real.exp_pos 16) hJe
    rw [Real.log_exp] at hh
    exact hh.le
  have hp : (J : ℝ) ≤ (J : ℝ) ^ 10 := by
    simpa using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ J) (show 1 ≤ 10 by omega)
  refine ⟨(J : ℝ) ^ 10, by linarith, LargeL223.principalCfg J, ⟨J, hJ, hlog, rfl, rfl⟩, ?_⟩
  refine ⟨(((J : ℝ), (1 : DirichletCharacter ℂ 1))), ?_⟩
  apply mem_image.mpr
  exact ⟨0, mem_range.mpr (by omega), by rfl⟩

#print axioms old_lemma10_large_L_false
#print axioms bare_long_sup_false
#print axioms old_fgm_combine_remainders_false
#print axioms fgm_combine_remainders_instance
#print axioms old_fgm_discretization_error_false
#print axioms fgm_discretization_error_instance
#print axioms LeanLab.BakerHarmanPintz1997.DecompJ883.fgm_combine_remainders
#print axioms LeanLab.BakerHarmanPintz1997.lemma10_decomposed
#print axioms LeanLab.BakerHarmanPintz1997.longSup_of_reflection
#print axioms LeanLab.BakerHarmanPintz1997.theorem1_via_prop12
#print axioms lemma10_repaired_instance
#print axioms principal_sum_upper

end LeanLab.BakerHarmanPintz1997.Audit1609
