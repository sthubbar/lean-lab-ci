/-
P0076 J. Teräväinen, arXiv 1611.08585, Lemma 5.2, page 18, quoting Matomäki and Shao,
Vinogradov's three primes theorem with almost twin primes, Lemma 7.4.
The leaves `lemma52_dyad` and `lemma52_half` of `WeightedPrimeSplit` are proved here from one
general lemma for any order convex range `R N ⊆ range N`, from the single new leaf
`twisted_interval_bound`, the Fourier dual count of a short exponential sum over an interval.
The class indicator of `𝒬 (mod Q)` is expanded in additive characters, the premise on `𝒬`
bounds every nonzero frequency, and the Fourier complexity of `χ` reduces the twisted sums
`∑ χ(t - n) e(a n / Q)` to linear exponential sums over the interval.
AI wrote this Lean code, Claude, session CLOUD-S69, burst-20261122. Checked only by the Lean
kernel. The binary Goldbach conjecture is OPEN.
-/
import LeanLab.Teravainen2016.WeightedPrimeSplit

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-! ### The character `eC` -/

private theorem eC_add1122b (x y : ℝ) : eC (x + y) = eC x * eC y := by
  unfold eC; rw [← Complex.exp_add]; congr 1; push_cast; ring

private theorem eC_norm1122b (x : ℝ) : ‖eC x‖ = 1 := by
  unfold eC
  rw [Complex.norm_exp]
  have h : (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)).re = 0 := by simp
  rw [h, Real.exp_zero]

private theorem eC_conj1122b (x : ℝ) : (starRingEnd ℂ) (eC x) = eC (-x) := by
  unfold eC
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

private theorem eC_nat_mul1122b (k : ℕ) (x : ℝ) : eC ((k : ℝ) * x) = (eC x) ^ k := by
  unfold eC; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

private theorem eC_int1122b (m : ℤ) : eC (m : ℝ) = 1 := by
  unfold eC
  rw [Complex.exp_eq_one_iff]
  exact ⟨m, by push_cast; ring⟩

private theorem eC_eq_one_iff1122b (x : ℝ) : eC x = 1 ↔ ∃ m : ℤ, x = m := by
  unfold eC
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h : (2 * Real.pi * Complex.I) * (x : ℂ) = (2 * Real.pi * Complex.I) * (n : ℂ) := by
      rw [hn]; ring
    have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have := mul_left_cancel₀ hne h
    exact_mod_cast this
  · rintro ⟨m, rfl⟩
    exact ⟨m, by push_cast; ring⟩

/-! ### Orthogonality of additive characters modulo `Q` -/

/-- `∑_{a mod Q} e(a m / Q) = Q 1_{Q ∣ m}`. -/
theorem orth1122b (Q : ℕ) (hQ : 1 ≤ Q) (m : ℤ) :
    ∑ a ∈ range Q, eC ((a : ℝ) * m / Q) = if (Q : ℤ) ∣ m then (Q : ℂ) else 0 := by
  have hQ' : (Q : ℝ) ≠ 0 := by
    have : (0 : ℝ) < Q := by exact_mod_cast hQ
    exact this.ne'
  have hterm : ∀ a : ℕ, eC ((a : ℝ) * m / Q) = eC ((m : ℝ) / Q) ^ a := by
    intro a; rw [← eC_nat_mul1122b]; congr 1; ring
  simp_rw [hterm]
  split_ifs with h
  · obtain ⟨j, rfl⟩ := h
    have : eC ((Q : ℝ) * (j : ℝ) / Q) = 1 := by
      rw [show (Q : ℝ) * (j : ℝ) / Q = (j : ℝ) by field_simp]
      exact eC_int1122b j
    push_cast
    simp [this]
  · have hne : eC ((m : ℝ) / Q) ≠ 1 := by
      rw [Ne, eC_eq_one_iff1122b]; rintro ⟨j, hj⟩
      apply h; refine ⟨j, ?_⟩
      have : (m : ℝ) = Q * j := by
        rw [div_eq_iff hQ'] at hj; linarith
      exact_mod_cast this
    rw [geom_sum_eq hne, ← eC_nat_mul1122b,
      show (Q : ℝ) * ((m : ℝ) / Q) = (m : ℝ) by field_simp, eC_int1122b]
    simp

theorem dvd_iff_mod1122b (Q n c : ℕ) (hc : c < Q) : (Q : ℤ) ∣ (n : ℤ) - c ↔ n % Q = c := by
  rw [← Int.modEq_iff_dvd, Int.ModEq, ← Int.natCast_mod, ← Int.natCast_mod,
    Nat.mod_eq_of_lt hc]
  constructor <;> intro h <;> omega

/-! ### The new leaf -/

/-- LEAF: the Fourier dual count of a linear exponential sum over an interval, the step of
Matomäki and Shao Lemma 7.4 behind the error `Q C² √N` of Lemma 5.2, page 18. Class MEDIUM.
For an interval `S` of length at most `N`, `|∑_{n ∈ S} e(γ n)| ≤ min(|S|, 1/(2‖γ‖))`, and
summing over the `Q` frequencies `a/Q - β` gives at most `2N + Q (1 + log Q)`, which is at most
`K (N + Q √N)` once `6 Q² ≤ N`. -/
theorem twisted_interval_bound : ∃ K : ℝ, 0 < K ∧ ∀ N Q : ℕ, 1 ≤ Q → 6 * Q ^ 2 ≤ N →
    ∀ S : Finset ℕ, S ⊆ range N → (∀ x ∈ S, ∀ z ∈ S, ∀ y, x ≤ y → y ≤ z → y ∈ S) →
    ∀ β : ℝ, ∑ a ∈ range Q, ‖∑ n ∈ S, eC (((a : ℝ) / Q - β) * n)‖ ≤
      K * (N + Q * Real.sqrt N) := by
  sorry

/-! ### The coefficient bound from the premise on `𝒬` -/

theorem coef_bound1122b (Q : ℕ) (𝒬 : Finset ℕ) (η₀ : ℝ)
    (hexp : ∀ q a : ℕ, q ∣ Q → q ≠ 1 → 0 < a → a.Coprime q →
        ‖∑ c₀ ∈ 𝒬, eC ((a : ℝ) * c₀ / q)‖ ≤ η₀ * #𝒬)
    (a : ℕ) (ha0 : 0 < a) (haQ : a < Q) :
    ‖∑ c ∈ 𝒬, eC (-((a : ℝ) * c / Q))‖ ≤ η₀ * #𝒬 := by
  set g := Nat.gcd a Q with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ ha0
  have hga : g ∣ a := Nat.gcd_dvd_left a Q
  have hgQ : g ∣ Q := Nat.gcd_dvd_right a Q
  have hcop : (a / g).Coprime (Q / g) := Nat.coprime_div_gcd_div_gcd hgpos
  have hqdvd : Q / g ∣ Q := Nat.div_dvd_of_dvd hgQ
  have hapos : 0 < a / g := Nat.div_pos (Nat.le_of_dvd ha0 hga) hgpos
  have hq1 : Q / g ≠ 1 := by
    intro h1
    have hQg : Q = g := by
      have := Nat.mul_div_cancel' hgQ
      rw [h1, mul_one] at this; exact this.symm
    have : g ≤ a := Nat.le_of_dvd ha0 hga
    omega
  have hbound := hexp (Q / g) (a / g) hqdvd hq1 hapos hcop
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hgpos.ne'
  have hQpos : 0 < Q := by omega
  have hQR : (Q : ℝ) ≠ 0 := by exact_mod_cast hQpos.ne'
  have hconv : ∀ c : ℕ, ((a / g : ℕ) : ℝ) * c / ((Q / g : ℕ) : ℝ) = (a : ℝ) * c / Q := by
    intro c
    rw [Nat.cast_div hga hgR, Nat.cast_div hgQ hgR]
    field_simp
  simp_rw [hconv] at hbound
  have hc : ∑ c ∈ 𝒬, eC (-((a : ℝ) * c / Q)) =
      (starRingEnd ℂ) (∑ c ∈ 𝒬, eC ((a : ℝ) * c / Q)) := by
    rw [map_sum]; simp_rw [eC_conj1122b]
  rw [hc, Complex.norm_conj]
  exact hbound

/-! ### The general lemma -/

/-- Lemma 5.2, page 18, on any order convex range `R N ⊆ range N`, from the leaf
`twisted_interval_bound`. -/
theorem lemma52On_of_twisted (R : ℕ → Finset ℕ) (hsub : ∀ N, R N ⊆ range N)
    (hconv : ∀ N, ∀ x ∈ R N, ∀ z ∈ R N, ∀ y, x ≤ y → y ≤ z → y ∈ R N)
    (htw : ∃ K : ℝ, 0 < K ∧ ∀ N Q : ℕ, 1 ≤ Q → 6 * Q ^ 2 ≤ N →
      ∀ S : Finset ℕ, S ⊆ range N → (∀ x ∈ S, ∀ z ∈ S, ∀ y, x ≤ y → y ≤ z → y ∈ S) →
      ∀ β : ℝ, ∑ a ∈ range Q, ‖∑ n ∈ S, eC (((a : ℝ) / Q - β) * n)‖ ≤
        K * (N + Q * Real.sqrt N)) :
    Lemma52On R := by
  obtain ⟨K, hK, hKb⟩ := htw
  refine ⟨2 * K, by positivity, ?_⟩
  intro Cc χ hχ0 hχC N Q hQ hNQ 𝒬 h𝒬 hne η₀ hη₀ hexp t
  obtain ⟨cf, α, hcf, hχ⟩ := hχC
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hQR : (Q : ℝ) ≠ 0 := hQpos.ne'
  have h𝒬pos : (0 : ℝ) < #𝒬 := by exact_mod_cast hne.card_pos
  set S := R N with hS
  set f : ℕ → ℝ := fun n => χ (t - n) with hf
  -- the twisted sums
  set T : ℕ → ℂ := fun a => ∑ n ∈ S, (f n : ℂ) * eC ((a : ℝ) * n / Q) with hT
  set G : Fin Cc → ℕ → ℂ := fun k a => ∑ n ∈ S, eC (((a : ℝ) / Q - α k) * n) with hG
  have hTexp : ∀ a, T a = ∑ k, cf k * eC (α k * t) * G k a := by
    intro a
    simp only [hT, hG, hf, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hχ (t - n), Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, mul_assoc, ← eC_add1122b, ← eC_add1122b]
    congr 2
    push_cast
    ring
  have hTnorm : ∀ a, ‖T a‖ ≤ ∑ k, (Cc : ℝ) * ‖G k a‖ := by
    intro a
    rw [hTexp a]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_mul, eC_norm1122b, mul_one]
    exact mul_le_mul_of_nonneg_right (hcf k) (norm_nonneg _)
  have hTsum : ∑ a ∈ range Q, ‖T a‖ ≤ (Cc : ℝ) * (Cc * (K * (N + Q * Real.sqrt N))) := by
    calc ∑ a ∈ range Q, ‖T a‖ ≤ ∑ a ∈ range Q, ∑ k, (Cc : ℝ) * ‖G k a‖ :=
          Finset.sum_le_sum fun a _ => hTnorm a
      _ = (Cc : ℝ) * ∑ k, ∑ a ∈ range Q, ‖G k a‖ := by
          rw [Finset.sum_comm, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
      _ ≤ (Cc : ℝ) * ∑ _k : Fin Cc, K * (N + Q * Real.sqrt N) := by
          gcongr with k
          exact hKb N Q hQ hNQ S (hsub N) (hconv N) (α k)
      _ = (Cc : ℝ) * (Cc * (K * (N + Q * Real.sqrt N))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- the expansion of the class indicator
  set coef : ℕ → ℂ := fun a => ∑ c ∈ 𝒬, eC (-((a : ℝ) * c / Q)) with hcoef
  set F : ℝ := ∑ c₀ ∈ 𝒬, ∑ n ∈ S.filter (fun n => n % Q = c₀), f n with hF
  have hexpand : ((Q : ℝ) * F : ℂ) = ∑ a ∈ range Q, coef a * T a := by
    have h1 : F = ∑ n ∈ S, ∑ c ∈ 𝒬, if n % Q = c then f n else 0 := by
      rw [hF]
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
    have h2 : ∑ a ∈ range Q, coef a * T a =
        ∑ a ∈ range Q, ∑ n ∈ S, ∑ c ∈ 𝒬,
          (f n : ℂ) * eC ((a : ℝ) * (((n : ℤ) - c : ℤ) : ℝ) / Q) := by
      simp only [hcoef, hT, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun n _ =>
        Finset.sum_congr rfl fun c _ => ?_
      have hadd := eC_add1122b ((a : ℝ) * n / Q) (-((a : ℝ) * c / Q))
      rw [show ((a : ℝ) * (((n : ℤ) - c : ℤ) : ℝ) / Q) = (a : ℝ) * n / Q + -((a : ℝ) * c / Q) by
        push_cast; ring, hadd]
      ring
    have h3 : ∑ a ∈ range Q, ∑ n ∈ S, ∑ c ∈ 𝒬,
          (f n : ℂ) * eC ((a : ℝ) * (((n : ℤ) - c : ℤ) : ℝ) / Q) =
        ∑ n ∈ S, ∑ c ∈ 𝒬, (f n : ℂ) *
          ∑ a ∈ range Q, eC ((a : ℝ) * (((n : ℤ) - c : ℤ) : ℝ) / Q) := by
      simp_rw [Finset.mul_sum]
      conv_lhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.sum_comm]
    have h4 : ∀ n ∈ S, ∀ c ∈ 𝒬, (f n : ℂ) *
          ∑ a ∈ range Q, eC ((a : ℝ) * (((n : ℤ) - c : ℤ) : ℝ) / Q) =
        (f n : ℂ) * (if n % Q = c then (Q : ℂ) else 0) := by
      intro n _ c hc
      have hcQ : c < Q := Finset.mem_range.1 (h𝒬 hc)
      rw [orth1122b Q hQ]
      by_cases h : n % Q = c
      · rw [if_pos ((dvd_iff_mod1122b Q n c hcQ).2 h), if_pos h]
      · rw [if_neg (mt (dvd_iff_mod1122b Q n c hcQ).1 h), if_neg h]
    rw [h2, h3, h1, Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [h4 n hn c hc]
    split_ifs <;> simp; ring
  -- the frequency `a = 0`
  have h0 : coef 0 * T 0 = (((#𝒬 : ℝ) * ∑ n ∈ S, f n : ℝ) : ℂ) := by
    simp [hcoef, hT, eC]
  have hQmem : 0 ∈ range Q := Finset.mem_range.2 (by omega)
  have hre : (Q : ℝ) * F = (#𝒬 : ℝ) * (∑ n ∈ S, f n) +
      (∑ a ∈ (range Q).erase 0, coef a * T a).re := by
    have := congrArg Complex.re hexpand
    have hcast : ((Q : ℝ) : ℂ) * (F : ℂ) = (((Q : ℝ) * F : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, Complex.ofReal_re, ← Finset.add_sum_erase _ _ hQmem, Complex.add_re, h0,
      Complex.ofReal_re] at this
    exact this
  have hrest : -(η₀ * #𝒬 * ∑ a ∈ range Q, ‖T a‖) ≤
      (∑ a ∈ (range Q).erase 0, coef a * T a).re := by
    have hn : ‖∑ a ∈ (range Q).erase 0, coef a * T a‖ ≤ η₀ * #𝒬 * ∑ a ∈ range Q, ‖T a‖ := by
      calc ‖∑ a ∈ (range Q).erase 0, coef a * T a‖
          ≤ ∑ a ∈ (range Q).erase 0, ‖coef a * T a‖ := norm_sum_le _ _
        _ ≤ ∑ a ∈ (range Q).erase 0, η₀ * #𝒬 * ‖T a‖ := by
            refine Finset.sum_le_sum fun a ha => ?_
            rw [norm_mul]
            have ha0 : a ≠ 0 := Finset.ne_of_mem_erase ha
            have haQ : a < Q := Finset.mem_range.1 (Finset.mem_of_mem_erase ha)
            exact mul_le_mul_of_nonneg_right
              (coef_bound1122b Q 𝒬 η₀ hexp a (Nat.pos_of_ne_zero ha0) haQ) (norm_nonneg _)
        _ = η₀ * #𝒬 * ∑ a ∈ (range Q).erase 0, ‖T a‖ := by rw [Finset.mul_sum]
        _ ≤ η₀ * #𝒬 * ∑ a ∈ range Q, ‖T a‖ := by
            gcongr
            exact Finset.erase_subset _ _
    have := Complex.abs_re_le_norm (∑ a ∈ (range Q).erase 0, coef a * T a)
    have := neg_abs_le (∑ a ∈ (range Q).erase 0, coef a * T a).re
    linarith
  -- arithmetic
  have hNR : ((6 * Q ^ 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast hNQ
  push_cast at hNR
  have hQs : (Q : ℝ) * Real.sqrt N ≤ N := by
    have hq : (Q : ℝ) ≤ Real.sqrt N := Real.le_sqrt_of_sq_le (by nlinarith)
    calc (Q : ℝ) * Real.sqrt N ≤ Real.sqrt N * Real.sqrt N :=
          mul_le_mul_of_nonneg_right hq (Real.sqrt_nonneg _)
      _ = N := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hstep : η₀ * ∑ a ∈ range Q, ‖T a‖ ≤ 2 * K * (η₀ * (Cc : ℝ) ^ 2 * N) := by
    calc η₀ * ∑ a ∈ range Q, ‖T a‖ ≤ η₀ * ((Cc : ℝ) * (Cc * (K * (N + Q * Real.sqrt N)))) :=
          mul_le_mul_of_nonneg_left hTsum hη₀.le
      _ ≤ η₀ * ((Cc : ℝ) * (Cc * (K * (N + N)))) := by gcongr
      _ = 2 * K * (η₀ * (Cc : ℝ) ^ 2 * N) := by ring
  have hextra : 0 ≤ 2 * K * ((Q : ℝ) * (Cc : ℝ) ^ 2 * Real.sqrt N) := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ h𝒬pos]
  nlinarith [mul_le_mul_of_nonneg_left hstep h𝒬pos.le, mul_nonneg h𝒬pos.le hextra]

/-! ### The two ranges are order convex -/

theorem dyad_convex1122b (N : ℕ) :
    ∀ x ∈ dyad N, ∀ z ∈ dyad N, ∀ y, x ≤ y → y ≤ z → y ∈ dyad N := by
  intro x hx z hz y hxy hyz
  simp only [dyad, Finset.mem_filter, Finset.mem_range] at hx hz ⊢
  have hxy' : (x : ℝ) ≤ y := by exact_mod_cast hxy
  have hyz' : (y : ℝ) ≤ z := by exact_mod_cast hyz
  exact ⟨by omega, by linarith [hx.2.1], by linarith [hz.2.2]⟩

theorem half_convex1122b (N : ℕ) :
    ∀ x ∈ half N, ∀ z ∈ half N, ∀ y, x ≤ y → y ≤ z → y ∈ half N := by
  intro x hx z hz y hxy hyz
  simp only [half, Finset.mem_filter, Finset.mem_range] at hx hz ⊢
  have hxy' : (x : ℝ) ≤ y := by exact_mod_cast hxy
  have hyz' : (y : ℝ) ≤ z := by exact_mod_cast hyz
  exact ⟨by omega, by linarith [hx.2.1], by linarith [hz.2.2]⟩

/-! ### The assemblies -/

/-- `lemma52_dyad` from the leaf `twisted_interval_bound`. -/
theorem lemma52_dyad_of_leaves : Lemma52On dyad :=
  lemma52On_of_twisted dyad (fun _ => Finset.filter_subset _ _) dyad_convex1122b
    twisted_interval_bound

/-- `lemma52_half` from the leaf `twisted_interval_bound`. -/
theorem lemma52_half_of_leaves : Lemma52On half :=
  lemma52On_of_twisted half (fun _ => Finset.filter_subset _ _) half_convex1122b
    twisted_interval_bound

theorem lemma52_dyad_twin : type_of% @LeanLab.Teravainen2016.lemma52_dyad :=
  lemma52_dyad_of_leaves

theorem lemma52_half_twin : type_of% @LeanLab.Teravainen2016.lemma52_half :=
  lemma52_half_of_leaves

end LeanLab.Teravainen2016
