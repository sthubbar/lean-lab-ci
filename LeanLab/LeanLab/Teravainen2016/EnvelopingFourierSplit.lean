/-
P0076, Section 4, Proposition 4.1 iv and v, pages 13 and 16 to 17, display 4.5.
Split of the Fourier decay input `paper_enveloping_fourier_decay_input` of
MainInputsRestriction.lean into a finite Fourier inversion, a support statement,
the Selberg normalization v 1 0 = 1, and the cited Ramare and Ruzsa decay bound.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.MainInputsRestriction

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- Display 4.3 as a function of the transported representative t, before the
substitution t equal to n, or M when n is 0. Its period divides P of z. -/
noncomputable def envelopingF (w : ℕ) (W b : ℤ) (M t : ℕ) : ℝ :=
  envelopingG w 1 ((M : ℝ) ^ ((1 : ℝ) / 10)) *
    (∑ d ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors.filter
      (fun d => EnvelopingSifted w d (W * t + b)),
        envelopingRho w d ((M : ℝ) ^ ((1 : ℝ) / 10))) ^ 2

/-- Display 4.5 read as a finite Fourier coefficient: the discrete Fourier coefficient
of the P of z periodic function in display 4.3 at frequency a over q. -/
noncomputable def envelopingVraw (w : ℕ) (W b : ℤ) (M q a : ℕ) : ℂ :=
  (1 / (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10)) : ℂ)) *
    ∑ s ∈ range (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))),
      (envelopingF w W b M s : ℂ) * eC ((a : ℝ) * s / q)

/-- Display 4.5 with the support recorded on page 16: v of a over q is taken only for
q dividing P of z, square free and coprime to W, and a reduced residue mod q. -/
noncomputable def envelopingV (w : ℕ) (W b : ℤ) (M q a : ℕ) : ℂ :=
  if q ∣ envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10)) ∧ Squarefree q ∧
      Nat.Coprime q W.natAbs ∧ a < q ∧ Nat.Coprime a q
  then envelopingVraw w W b M q a else 0

/-- Display 4.3 equals the periodic function at the transported representative. -/
theorem envelopingBeta_eq_F (w : ℕ) (W b : ℤ) (M n : ℕ) :
    envelopingBeta w W b M n = envelopingF w W b M (if n = 0 then M else n) := rfl

/-- Page 15: display 4.3 is periodic in t with period P of z, since each prime p of a
divisor d of P of z divides P of z and membership in A_d only depends on W t + b mod d. -/
theorem envelopingF_mod (w : ℕ) (W b : ℤ) (M t : ℕ) :
    envelopingF w W b M t =
      envelopingF w W b M (t % envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))) := by
  unfold envelopingF
  set P := envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10)) with hPdef
  have hfilt : P.divisors.filter (fun d => EnvelopingSifted w d (W * (t : ℤ) + b)) =
      P.divisors.filter (fun d => EnvelopingSifted w d (W * ((t % P : ℕ) : ℤ) + b)) := by
    apply filter_congr
    intro d hd
    have hdP := Nat.dvd_of_mem_divisors hd
    unfold EnvelopingSifted
    apply and_congr_right
    intro _
    apply forall₂_congr
    intro p hp
    apply and_congr_right
    intro _
    obtain ⟨c, hc⟩ := dvd_trans (Nat.dvd_of_mem_primeFactors hp) hdP
    have h' : (t : ℤ) = (P : ℤ) * ((t / P : ℕ) : ℤ) + ((t % P : ℕ) : ℤ) := by
      exact_mod_cast (Nat.div_add_mod t P).symm
    have key : W * (t : ℤ) + b =
        W * ((t % P : ℕ) : ℤ) + b + (p : ℤ) * (W * c * ((t / P : ℕ) : ℤ)) := by
      rw [h', hc]; push_cast; ring
    have key1 : W * (t : ℤ) + b - 1 =
        (W * ((t % P : ℕ) : ℤ) + b - 1) + (p : ℤ) * (W * c * ((t / P : ℕ) : ℤ)) := by
      rw [key]; ring
    rw [key1, key, dvd_add_left (dvd_mul_right _ _), dvd_add_left (dvd_mul_right _ _)]
  rw [hfilt]

/-- Additivity of the additive character. -/
theorem efs_eC_add (x y : ℝ) : eC (x + y) = eC x * eC y := by
  unfold eC
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Natural multiples in the additive character. -/
theorem efs_eC_nat_mul (k : ℕ) (x : ℝ) : eC ((k : ℝ) * x) = (eC x) ^ k := by
  unfold eC
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The additive character is 1 at integers. -/
theorem efs_eC_int (m : ℤ) : eC ((m : ℝ)) = 1 := by
  rw [show eC ((m : ℝ)) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ)) from rfl]
  rw [show (2 * (Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ)) =
    (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
  rw [Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]

/-- The additive character is 1 only at integers. -/
theorem efs_eC_eq_one {y : ℝ} (h : eC y = 1) : ∃ m : ℤ, y = m := by
  unfold eC at h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  refine ⟨n, ?_⟩
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  have : ((y : ℝ) : ℂ) = (n : ℂ) := by
    apply mul_left_cancel₀ h2
    rw [hn]
    ring
  exact_mod_cast this

/-- Orthogonality of the additive characters mod P. -/
theorem efs_orth (P : ℕ) (hP : P ≠ 0) (x : ℤ) :
    ∑ k ∈ range P, eC ((k : ℝ) * x / P) = if (P : ℤ) ∣ x then (P : ℂ) else 0 := by
  have hPr : (P : ℝ) ≠ 0 := by exact_mod_cast hP
  have hterm : ∀ k : ℕ, eC ((k : ℝ) * x / P) = eC ((x : ℝ) / P) ^ k := by
    intro k
    rw [← efs_eC_nat_mul]
    congr 1
    ring
  rw [sum_congr rfl (fun k _ => hterm k)]
  split_ifs with h
  · obtain ⟨m, hm⟩ := h
    have h1 : eC ((x : ℝ) / P) = 1 := by
      rw [hm]
      push_cast
      rw [show ((P : ℝ) * m / P) = (m : ℝ) by field_simp]
      exact efs_eC_int m
    simp [h1]
  · have hne : eC ((x : ℝ) / P) ≠ 1 := by
      intro h1
      obtain ⟨m, hm⟩ := efs_eC_eq_one h1
      apply h
      refine ⟨m, ?_⟩
      have : (x : ℝ) = (P : ℝ) * m := by
        rw [div_eq_iff hPr] at hm
        rw [hm]
        ring
      exact_mod_cast this
    rw [geom_sum_eq hne]
    have h2 : eC ((x : ℝ) / P) ^ P = 1 := by
      rw [← efs_eC_nat_mul, show (P : ℝ) * ((x : ℝ) / P) = (x : ℝ) by field_simp]
      exact efs_eC_int x
    rw [h2, sub_self, zero_div]

/-- Reindexing the fractions k over P by their reduced forms a over q with q dividing P. -/
theorem efs_reindex (P : ℕ) (hP : P ≠ 0) (x : ℝ) :
    ∑ q ∈ P.divisors, ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      eC ((a : ℝ) * x / q) = ∑ k ∈ range P, eC ((k : ℝ) * x / P) := by
  rw [Finset.sum_sigma']
  apply Finset.sum_bij (fun (qa : Σ _ : ℕ, ℕ) _ => qa.2 * (P / qa.1))
  · rintro ⟨q, a⟩ h
    simp only [mem_sigma, mem_filter, mem_range, Nat.mem_divisors] at h
    obtain ⟨⟨hqP, -⟩, haq, -⟩ := h
    simp only [mem_range]
    have hq0 : 0 < q := Nat.pos_of_dvd_of_pos hqP (Nat.pos_of_ne_zero hP)
    calc a * (P / q) < q * (P / q) :=
          Nat.mul_lt_mul_of_pos_right haq
            (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hP) hqP) hq0)
      _ = P := Nat.mul_div_cancel' hqP
  · rintro ⟨q1, a1⟩ h1 ⟨q2, a2⟩ h2 heq
    simp only [mem_sigma, mem_filter, mem_range, Nat.mem_divisors] at h1 h2
    simp only at heq
    obtain ⟨⟨hq1P, -⟩, -, hc1⟩ := h1
    obtain ⟨⟨hq2P, -⟩, -, hc2⟩ := h2
    have hmul : a1 * q2 * P = a2 * q1 * P := by
      calc a1 * q2 * P = a1 * (P / q1) * q1 * q2 := by
            rw [mul_assoc a1 (P / q1) q1, Nat.div_mul_cancel hq1P]; ring
        _ = a2 * (P / q2) * q1 * q2 := by rw [heq]
        _ = a2 * q1 * (P / q2 * q2) := by ring
        _ = a2 * q1 * P := by rw [Nat.div_mul_cancel hq2P]
    have key : a1 * q2 = a2 * q1 := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hP) hmul
    have hd1 : q1 ∣ q2 := Nat.Coprime.dvd_of_dvd_mul_left hc1.symm ⟨a2, by linarith [key]⟩
    have hd2 : q2 ∣ q1 := Nat.Coprime.dvd_of_dvd_mul_left hc2.symm ⟨a1, by linarith [key]⟩
    have hq : q1 = q2 := Nat.dvd_antisymm hd1 hd2
    subst hq
    have hq0 : 0 < q1 := Nat.pos_of_dvd_of_pos hq1P (Nat.pos_of_ne_zero hP)
    have ha : a1 = a2 := Nat.eq_of_mul_eq_mul_right hq0 key
    subst ha
    rfl
  · intro k hk
    have hk' : k < P := mem_range.mp hk
    have hg0 : 0 < Nat.gcd k P := Nat.gcd_pos_of_pos_right k (Nat.pos_of_ne_zero hP)
    refine ⟨⟨P / Nat.gcd k P, k / Nat.gcd k P⟩, ?_, ?_⟩
    · simp only [mem_sigma, mem_filter, mem_range, Nat.mem_divisors]
      refine ⟨⟨Nat.div_dvd_of_dvd (Nat.gcd_dvd_right k P), hP⟩, ?_,
        Nat.coprime_div_gcd_div_gcd hg0⟩
      exact Nat.div_lt_div_of_lt_of_dvd (Nat.gcd_dvd_right k P) hk'
    · show k / Nat.gcd k P * (P / (P / Nat.gcd k P)) = k
      rw [Nat.div_div_self (Nat.gcd_dvd_right k P) hP,
        Nat.div_mul_cancel (Nat.gcd_dvd_left k P)]
  · rintro ⟨q, a⟩ h
    simp only [mem_sigma, mem_filter, mem_range, Nat.mem_divisors] at h
    obtain ⟨⟨hqP, -⟩, -, -⟩ := h
    have hq0 : (q : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.pos_of_dvd_of_pos hqP (Nat.pos_of_ne_zero hP)).ne'
    have hPr : (P : ℝ) ≠ 0 := by exact_mod_cast hP
    congr 1
    push_cast [Nat.cast_div hqP hq0]
    field_simp

/-- Proposition 4.1 v, page 16, the finite Fourier inversion on Z mod P behind formula 4.1
of the paper, as in Ramare and Ruzsa reference 18 formula 4.1.13. A P periodic function
equals the sum over the reduced fractions a over q, q dividing P, of its discrete Fourier
coefficients. -/
theorem dft_inversion_divisors (P : ℕ) (hP : P ≠ 0) (f : ℕ → ℂ)
    (hf : ∀ t, f t = f (t % P)) (t : ℕ) :
    f t = ∑ q ∈ P.divisors, ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      ((1 / (P : ℂ)) * ∑ s ∈ range P, f s * eC ((a : ℝ) * s / q)) *
        eC (-((a : ℝ) * t / q)) := by
  have hPc : (P : ℂ) ≠ 0 := by exact_mod_cast hP
  have step : ∀ q a : ℕ, ((1 / (P : ℂ)) * ∑ s ∈ range P, f s * eC ((a : ℝ) * s / q)) *
      eC (-((a : ℝ) * t / q)) =
        ∑ s ∈ range P, (1 / (P : ℂ)) * f s * eC ((a : ℝ) * ((s : ℝ) - t) / q) := by
    intro q a
    rw [mul_assoc, sum_mul, mul_sum]
    apply sum_congr rfl
    intro s _
    rw [show (a : ℝ) * ((s : ℝ) - t) / q = a * s / q + -(a * t / q) by ring, efs_eC_add]
    ring
  symm
  calc _ = ∑ q ∈ P.divisors, ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ∑ s ∈ range P, (1 / (P : ℂ)) * f s * eC ((a : ℝ) * ((s : ℝ) - t) / q) := by
        apply sum_congr rfl; intro q _; apply sum_congr rfl; intro a _; exact step q a
    _ = ∑ s ∈ range P, ∑ q ∈ P.divisors, ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        (1 / (P : ℂ)) * f s * eC ((a : ℝ) * ((s : ℝ) - t) / q) := by
        rw [← sum_comm]
        apply sum_congr rfl; intro q _
        exact sum_comm
    _ = ∑ s ∈ range P, (1 / (P : ℂ)) * f s *
        ∑ q ∈ P.divisors, ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          eC ((a : ℝ) * ((s : ℝ) - t) / q) := by
        apply sum_congr rfl; intro s _
        rw [mul_sum]; apply sum_congr rfl; intro q _; rw [mul_sum]
    _ = ∑ s ∈ range P, (1 / (P : ℂ)) * f s *
        (if (P : ℤ) ∣ ((s : ℤ) - t) then (P : ℂ) else 0) := by
        apply sum_congr rfl; intro s _
        rw [efs_reindex P hP, ← efs_orth P hP]
        congr 1
        apply sum_congr rfl; intro k _
        congr 1
        push_cast
        ring
    _ = f t := by
        rw [sum_eq_single (t % P)]
        · have hd : (P : ℤ) ∣ ((t % P : ℕ) : ℤ) - t :=
            Nat.modEq_iff_dvd.mp (Nat.mod_modEq t P).symm
          rw [if_pos hd, ← hf]
          field_simp
        · intro s hs hne
          rw [if_neg, mul_zero]
          intro hd
          apply hne
          have hm : t % P = s % P := Nat.modEq_iff_dvd.mpr hd
          rw [hm, Nat.mod_eq_of_lt (mem_range.mp hs)]
        · intro h
          exact absurd (mem_range.mpr (Nat.mod_lt t (Nat.pos_of_ne_zero hP))) h

/-- The prime product P of z is nonzero. -/
theorem envelopingPrimeProduct_ne_zero (w : ℕ) (z : ℝ) : envelopingPrimeProduct w z ≠ 0 := by
  rw [envelopingPrimeProduct]
  exact prod_ne_zero_iff.mpr (fun p hp => (mem_filter.mp hp).2.1.ne_zero)

/-- Proposition 4.1 v, page 16, finite Fourier inversion behind formula 4.1, proved from
the periodicity of display 4.3 and the discrete Fourier inversion leaf. -/
theorem enveloping_fourier_inversion (w : ℕ) (W b : ℤ) (M t : ℕ) :
    (envelopingF w W b M t : ℂ) =
      ∑ q ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors,
        ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          envelopingVraw w W b M q a * eC (-((a : ℝ) * t / q)) :=
  dft_inversion_divisors _ (envelopingPrimeProduct_ne_zero _ _)
    (fun s => (envelopingF w W b M s : ℂ))
    (fun s => congrArg (fun x : ℝ => (x : ℂ)) (envelopingF_mod w W b M s)) t

/-- Splitting a sum over range of L times m into m blocks of length L. -/
theorem efs_sum_range_mul {β : Type*} [AddCommMonoid β] (L m : ℕ) (f : ℕ → β) :
    ∑ s ∈ range (L * m), f s = ∑ j ∈ range m, ∑ r ∈ range L, f (L * j + r) := by
  induction m with
  | zero => simp
  | succ m ih => rw [show L * (m + 1) = L * m + L by ring, sum_range_add, ih, sum_range_succ]

/-- Page 15: membership in A_d depends on t only mod any multiple L of d. -/
theorem efs_sifted_shift (w d : ℕ) (W b : ℤ) (L r j : ℕ) (hdL : d ∣ L) :
    EnvelopingSifted w d (W * ((L * j + r : ℕ) : ℤ) + b) ↔
      EnvelopingSifted w d (W * (r : ℤ) + b) := by
  unfold EnvelopingSifted
  apply and_congr_right
  intro _
  apply forall₂_congr
  intro p hp
  apply and_congr_right
  intro _
  obtain ⟨c, hc⟩ := dvd_trans (Nat.dvd_of_mem_primeFactors hp) hdL
  have key : W * ((L * j + r : ℕ) : ℤ) + b = W * (r : ℤ) + b + (p : ℤ) * (W * c * j) := by
    rw [hc]; push_cast; ring
  have key1 : W * ((L * j + r : ℕ) : ℤ) + b - 1 =
      (W * (r : ℤ) + b - 1) + (p : ℤ) * (W * c * j) := by
    rw [key]; ring
  rw [key1, key, dvd_add_left (dvd_mul_right _ _), dvd_add_left (dvd_mul_right _ _)]

/-- An L periodic function has vanishing Fourier coefficient on Z mod P at a reduced
fraction a over q whose denominator does not divide L. -/
theorem efs_periodic_vanish (P L q a : ℕ) (hP : P ≠ 0) (hLP : L ∣ P) (hqP : q ∣ P)
    (hq : ¬ q ∣ L) (ha : Nat.Coprime a q) (g : ℕ → ℂ) (hg : ∀ j r, g (L * j + r) = g r) :
    ∑ s ∈ range P, g s * eC ((a : ℝ) * s / q) = 0 := by
  obtain ⟨m, hm⟩ := hLP
  have hq0 : (q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_dvd_of_pos hqP (Nat.pos_of_ne_zero hP)).ne'
  have hPm : (L : ℝ) * m = (P : ℝ) := by exact_mod_cast hm.symm
  rw [hm, efs_sum_range_mul]
  have hz : ∀ j r : ℕ, g (L * j + r) * eC ((a : ℝ) * ((L * j + r : ℕ) : ℝ) / q) =
      (g r * eC ((a : ℝ) * r / q)) * eC ((a : ℝ) * L / q) ^ j := by
    intro j r
    rw [hg, ← efs_eC_nat_mul, mul_assoc, ← efs_eC_add]
    congr 2
    push_cast
    ring
  rw [sum_congr rfl (fun j _ => sum_congr rfl (fun r _ => hz j r)), sum_comm]
  apply sum_eq_zero
  intro r _
  rw [← mul_sum]
  have hne : eC ((a : ℝ) * L / q) ≠ 1 := by
    intro h1
    obtain ⟨n, hn⟩ := efs_eC_eq_one h1
    apply hq
    have h2 : ((a * L : ℕ) : ℤ) = n * q := by
      have : ((a : ℝ) * L) = n * q := by rw [div_eq_iff hq0] at hn; exact hn
      exact_mod_cast this
    have h3 : q ∣ a * L := Int.natCast_dvd_natCast.mp ⟨n, by rw [h2]; ring⟩
    exact Nat.Coprime.dvd_of_dvd_mul_left ha.symm h3
  rw [geom_sum_eq hne]
  have h4 : eC ((a : ℝ) * L / q) ^ m = 1 := by
    rw [← efs_eC_nat_mul]
    obtain ⟨c, hc⟩ := hqP
    have hqc : (P : ℝ) = q * c := by exact_mod_cast hc
    have : (m : ℝ) * ((a : ℝ) * L / q) = (((a * c : ℕ) : ℤ) : ℝ) := by
      calc (m : ℝ) * ((a : ℝ) * L / q) = a * ((L : ℝ) * m) / q := by ring
        _ = a * ((q : ℝ) * c) / q := by rw [hPm, hqc]
        _ = (((a * c : ℕ) : ℤ) : ℝ) := by push_cast; field_simp
    rw [this]
    exact efs_eC_int _
  rw [h4, sub_self, zero_div, mul_zero]

/-- Page 15: rho_d vanishes for d above z, since then G_d of z is an empty sum. -/
theorem efs_rho_zero (w d : ℕ) {z : ℝ} (hd : z < d) : envelopingRho w d z = 0 := by
  have hG : envelopingG w d z = 0 := by
    unfold envelopingG
    rw [filter_eq_empty_iff.mpr, sum_empty]
    intro δ hδ hle
    have hδ1 : 1 ≤ δ := (mem_Icc.mp hδ).1
    have hdl : (d : ℝ) ≤ (Nat.lcm d δ : ℝ) := by
      rcases Nat.eq_zero_or_pos d with h0 | h0
      · rw [h0]; simp
      · exact_mod_cast Nat.le_of_dvd (Nat.lcm_pos h0 hδ1) (Nat.dvd_lcm_left d δ)
    linarith
  rw [envelopingRho, hG]
  simp

/-- Expansion of the square in display 4.3 as a double sum over d1 and d2. -/
theorem efs_F_expand (w : ℕ) (W b : ℤ) (M s : ℕ) :
    envelopingF w W b M s =
      ∑ d1 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors,
        ∑ d2 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors,
          envelopingG w 1 ((M : ℝ) ^ ((1 : ℝ) / 10)) *
            (if EnvelopingSifted w d1 (W * (s : ℤ) + b)
              then envelopingRho w d1 ((M : ℝ) ^ ((1 : ℝ) / 10)) else 0) *
            (if EnvelopingSifted w d2 (W * (s : ℤ) + b)
              then envelopingRho w d2 ((M : ℝ) ^ ((1 : ℝ) / 10)) else 0) := by
  unfold envelopingF
  rw [sum_filter, sq, sum_mul_sum, mul_sum]
  apply sum_congr rfl
  intro d1 _
  rw [mul_sum]
  apply sum_congr rfl
  intro d2 _
  ring

/-- Proposition 4.1 v, pages 16 to 17, support of v in display 4.5. Squaring display 4.3
gives a combination of functions of t periodic mod lcm d1 d2, which is at most z squared
equal M to the 1 over 5 whenever rho of d1 and rho of d2 are nonzero, so the coefficient at
a reduced a over q vanishes when q exceeds the floor of M to the 1 over 5. -/
theorem enveloping_vraw_vanish (w : ℕ) (W b : ℤ) (M q a : ℕ)
    (hq : q ∣ envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10)))
    (hqM : ⌊(M : ℝ) ^ ((1 : ℝ) / 5)⌋₊ < q) (ha : Nat.Coprime a q) :
    envelopingVraw w W b M q a = 0 := by
  have hzz : (M : ℝ) ^ ((1 : ℝ) / 10) * (M : ℝ) ^ ((1 : ℝ) / 10) = (M : ℝ) ^ ((1 : ℝ) / 5) := by
    rw [← Real.rpow_add' (Nat.cast_nonneg M) (by norm_num)]
    norm_num
  have hz0 : 0 ≤ (M : ℝ) ^ ((1 : ℝ) / 10) := Real.rpow_nonneg (Nat.cast_nonneg M) _
  unfold envelopingVraw
  simp only [efs_F_expand, Complex.ofReal_sum]
  generalize (M : ℝ) ^ ((1 : ℝ) / 10) = z at hq hzz hz0 ⊢
  have hP := envelopingPrimeProduct_ne_zero w z
  generalize envelopingPrimeProduct w z = P at hq hP ⊢
  rw [mul_eq_zero]
  right
  simp only [sum_mul]
  rw [sum_comm]
  apply sum_eq_zero
  intro d1 hd1
  rw [sum_comm]
  apply sum_eq_zero
  intro d2 hd2
  have hd1P := Nat.dvd_of_mem_divisors hd1
  have hd2P := Nat.dvd_of_mem_divisors hd2
  have hd1p := Nat.pos_of_mem_divisors hd1
  have hd2p := Nat.pos_of_mem_divisors hd2
  by_cases hsmall : (d1 : ℝ) ≤ z ∧ (d2 : ℝ) ≤ z
  · apply efs_periodic_vanish P (Nat.lcm d1 d2) q a hP (Nat.lcm_dvd hd1P hd2P) hq _ ha
    · intro j r
      simp only [efs_sifted_shift w d1 W b _ r j (Nat.dvd_lcm_left d1 d2),
        efs_sifted_shift w d2 W b _ r j (Nat.dvd_lcm_right d1 d2)]
    · intro hdvd
      have hL0 : 0 < Nat.lcm d1 d2 := Nat.lcm_pos hd1p hd2p
      have hqL := Nat.le_of_dvd hL0 hdvd
      have hLN : Nat.lcm d1 d2 ≤ ⌊(M : ℝ) ^ ((1 : ℝ) / 5)⌋₊ := by
        apply Nat.le_floor
        calc (Nat.lcm d1 d2 : ℝ) ≤ ((d1 * d2 : ℕ) : ℝ) := by
              exact_mod_cast Nat.le_of_dvd (Nat.mul_pos hd1p hd2p) (Nat.lcm_dvd_mul d1 d2)
          _ = (d1 : ℝ) * d2 := by push_cast; ring
          _ ≤ z * z := mul_le_mul hsmall.1 hsmall.2 (Nat.cast_nonneg _) hz0
          _ = _ := hzz
      omega
  · apply sum_eq_zero
    intro s _
    rw [not_and_or] at hsmall
    rcases hsmall with h | h
    · rw [efs_rho_zero w d1 (not_le.mp h)]
      simp
    · rw [efs_rho_zero w d2 (not_le.mp h)]
      simp

/-- Page 15, the local density g of d equal to the product of omega of p over p, the
proportion of residues t mod d with W t + b in A_d. -/
noncomputable def envelopingDensity (w d : ℕ) : ℝ :=
  ∏ p ∈ d.primeFactors, (envelopingOmega w p : ℝ) / p

/-- Page 16: every divisor of P of z is square free and coprime to W, since P of z is a
product of distinct primes above w and W has only prime factors at most w. -/
theorem enveloping_divisor_support {J w : ℕ} (hw : 5 ≤ w) {z : ℝ} {q : ℕ}
    (hq : q ∣ envelopingPrimeProduct w z) :
    Squarefree q ∧ Nat.Coprime q (WW J w).natAbs := by
  set S := (range (⌊z⌋₊ + 1)).filter (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ z) with hS
  have hP : envelopingPrimeProduct w z = ∏ p ∈ S, p := rfl
  have hprime : ∀ k : ℕ, k.Prime → k ∣ envelopingPrimeProduct w z → w < k := by
    intro k hk hkP
    rw [hP] at hkP
    obtain ⟨p, hp, hkp⟩ := (hk.prime.dvd_finsetProd_iff _).mp hkP
    have hp' := (mem_filter.mp hp).2
    rw [(Nat.prime_dvd_prime_iff_eq hk hp'.1).mp hkp]
    exact hp'.2.1
  constructor
  · apply Squarefree.squarefree_of_dvd hq
    rw [hP]
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i hi j hj hij
      exact Nat.coprime_iff_isRelPrime.mp
        ((Nat.coprime_primes (mem_filter.mp hi).2.1 (mem_filter.mp hj).2.1).mpr hij)
    · intro i hi
      exact (mem_filter.mp hi).2.1.prime.squarefree
  · apply Nat.coprime_of_dvd
    intro k hk hkq hkW
    have hwk := hprime k hk (dvd_trans hkq hq)
    have hkW' : (k : ℤ) ∣ Wmod J (Sw w) := Int.natCast_dvd.mpr hkW
    rcases prime_dvd_Wmod (fun r hr => (Sw_spec w r hr).1) hk hkW' with h | h | h
    · omega
    · omega
    · have := (mem_filter.mp h).1
      rw [mem_Icc] at this
      omega

/-- Chinese remainder theorem for sums over a full period m n with m and n coprime. -/
theorem efs_crt_sum (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (h : Nat.Coprime m n)
    (f g : ℕ → ℝ) :
    ∑ r ∈ range (m * n), f (r % m) * g (r % n) =
      (∑ x ∈ range m, f x) * (∑ y ∈ range n, g y) := by
  rw [sum_mul_sum, ← sum_product']
  apply sum_nbij (fun r => (r % m, r % n))
  · intro r _
    simp only [mem_product, mem_range]
    exact ⟨Nat.mod_lt r hm, Nat.mod_lt r hn⟩
  · intro r1 h1 r2 h2 heq
    simp only [Prod.mk.injEq] at heq
    have hmod := (Nat.modEq_and_modEq_iff_modEq_mul h).mp ⟨heq.1, heq.2⟩
    have e1 := Nat.mod_eq_of_lt (mem_range.mp (mem_coe.mp h1))
    have e2 := Nat.mod_eq_of_lt (mem_range.mp (mem_coe.mp h2))
    unfold Nat.ModEq at hmod
    rw [e1, e2] at hmod
    exact hmod
  · rintro ⟨x, y⟩ hxy
    simp only [coe_product, Set.mem_prod, mem_coe, mem_range] at hxy
    obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder h x y
    refine ⟨k % (m * n), ?_, ?_⟩
    · exact mem_coe.mpr (mem_range.mpr (Nat.mod_lt _ (Nat.mul_pos hm hn)))
    · simp only [Prod.mk.injEq]
      constructor
      · rw [Nat.mod_mod_of_dvd _ (dvd_mul_right m n)]
        unfold Nat.ModEq at hk1
        rw [hk1, Nat.mod_eq_of_lt hxy.1]
      · rw [Nat.mod_mod_of_dvd _ (dvd_mul_left n m)]
        unfold Nat.ModEq at hk2
        rw [hk2, Nat.mod_eq_of_lt hxy.2]
  · intro r _
    rfl

/-- One prime p not dividing W: the residues x mod p with p dividing W x + b, or with c and
p dividing W x + b minus 1, number 1, or 2 when c holds. -/
theorem efs_count_prime (W b : ℤ) (p : ℕ) (hp : p.Prime) (hW : ¬ (p : ℤ) ∣ W) (c : Prop) :
    ∑ x ∈ range p, (if ((p : ℤ) ∣ W * (x : ℤ) + b ∨ (c ∧ (p : ℤ) ∣ W * (x : ℤ) + b - 1))
      then (1 : ℝ) else 0) = if c then 2 else 1 := by
  haveI := Fact.mk hp
  have hu : (W : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hW
  have hcond : ∀ x : ℕ, ((p : ℤ) ∣ W * (x : ℤ) + b ∨ (c ∧ (p : ℤ) ∣ W * (x : ℤ) + b - 1)) ↔
      ((W : ZMod p) * (x : ZMod p) + (b : ZMod p) = 0 ∨
        (c ∧ (W : ZMod p) * (x : ZMod p) + (b : ZMod p) - 1 = 0)) := by
    intro x
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rfl
  simp only [hcond]
  have hrange : ∑ x ∈ range p, (if ((W : ZMod p) * (x : ZMod p) + (b : ZMod p) = 0 ∨
        (c ∧ (W : ZMod p) * (x : ZMod p) + (b : ZMod p) - 1 = 0)) then (1 : ℝ) else 0) =
      ∑ y : ZMod p, (if ((W : ZMod p) * y + (b : ZMod p) = 0 ∨
        (c ∧ (W : ZMod p) * y + (b : ZMod p) - 1 = 0)) then (1 : ℝ) else 0) := by
    apply sum_nbij (fun x : ℕ => (x : ZMod p))
    · intro x _
      exact mem_coe.mpr (mem_univ _)
    · intro x1 h1 x2 h2 heq
      have := congrArg ZMod.val heq
      simp only [ZMod.val_natCast] at this
      rwa [Nat.mod_eq_of_lt (mem_range.mp (mem_coe.mp h1)),
        Nat.mod_eq_of_lt (mem_range.mp (mem_coe.mp h2))] at this
    · intro y _
      exact ⟨y.val, mem_coe.mpr (mem_range.mpr (ZMod.val_lt y)), ZMod.natCast_zmod_val y⟩
    · intro x _
      rfl
  rw [hrange]
  have hbij : Function.Bijective (fun y : ZMod p => (W : ZMod p) * y + (b : ZMod p)) := by
    constructor
    · intro y1 y2 heq
      simp only [add_left_inj] at heq
      exact mul_left_cancel₀ hu heq
    · intro z
      refine ⟨((W : ZMod p))⁻¹ * (z - b), ?_⟩
      simp only
      rw [← mul_assoc, mul_inv_cancel₀ hu, one_mul, sub_add_cancel]
  rw [Fintype.sum_bijective _ hbij
    (fun y => (if ((W : ZMod p) * y + (b : ZMod p) = 0 ∨
        (c ∧ (W : ZMod p) * y + (b : ZMod p) - 1 = 0)) then (1 : ℝ) else 0))
    (fun z => (if (z = 0 ∨ (c ∧ z - 1 = 0)) then (1 : ℝ) else 0)) (fun y => rfl)]
  have h01 : (0 : ZMod p) ≠ 1 := zero_ne_one
  by_cases hc : c
  · have hsplit : ∀ z : ZMod p, (if (z = 0 ∨ (c ∧ z - 1 = 0)) then (1 : ℝ) else 0) =
        (if z = 0 then (1 : ℝ) else 0) + (if z = 1 then (1 : ℝ) else 0) := by
      intro z
      by_cases h0 : z = 0
      · subst h0; simp [h01]
      · by_cases h1 : z = 1
        · subst h1; simp [hc, h01.symm]
        · simp [h0, h1, sub_eq_zero]
    simp only [hsplit, sum_add_distrib, Fintype.sum_ite_eq', if_pos hc]
    norm_num
  · simp only [hc, false_and, or_false, Fintype.sum_ite_eq', if_false]

/-- Primes dividing P of z lie above w. -/
theorem efs_prime_gt {w : ℕ} {z : ℝ} {k : ℕ} (hk : k.Prime)
    (hkP : k ∣ envelopingPrimeProduct w z) : w < k := by
  rw [envelopingPrimeProduct] at hkP
  obtain ⟨p, hp, hkp⟩ := (hk.prime.dvd_finsetProd_iff _).mp hkP
  have hp' := (mem_filter.mp hp).2
  rw [(Nat.prime_dvd_prime_iff_eq hk hp'.1).mp hkp]
  exact hp'.2.1

/-- Page 15: A_d1 meets A_d2 in A of lcm d1 d2 for d1 and d2 dividing P of z. -/
theorem efs_sifted_lcm {w : ℕ} (hw : 5 ≤ w) {z : ℝ} {d1 d2 : ℕ}
    (hd1 : d1 ∣ envelopingPrimeProduct w z) (hd2 : d2 ∣ envelopingPrimeProduct w z) (m : ℤ) :
    (EnvelopingSifted w d1 m ∧ EnvelopingSifted w d2 m) ↔
      EnvelopingSifted w (Nat.lcm d1 d2) m := by
  have hP := envelopingPrimeProduct_ne_zero w z
  have h1 : d1 ≠ 0 := fun h => hP (Nat.eq_zero_of_zero_dvd (h ▸ hd1))
  have h2 : d2 ≠ 0 := fun h => hP (Nat.eq_zero_of_zero_dvd (h ▸ hd2))
  have hsq1 := (enveloping_divisor_support (J := 5) hw hd1).1
  have hsq2 := (enveloping_divisor_support (J := 5) hw hd2).1
  have hsqL := (enveloping_divisor_support (J := 5) hw (Nat.lcm_dvd hd1 hd2)).1
  unfold EnvelopingSifted
  have hpf : (Nat.lcm d1 d2).primeFactors = d1.primeFactors ∪ d2.primeFactors := by
    ext p
    simp only [Finset.mem_union, Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp, hpd, -⟩
      rcases (Nat.Prime.dvd_mul hp).mp (dvd_trans hpd (Nat.lcm_dvd_mul d1 d2)) with h | h
      · exact Or.inl ⟨hp, h, h1⟩
      · exact Or.inr ⟨hp, h, h2⟩
    · rintro (⟨hp, h, -⟩ | ⟨hp, h, -⟩)
      · exact ⟨hp, dvd_trans h (Nat.dvd_lcm_left _ _), Nat.lcm_ne_zero h1 h2⟩
      · exact ⟨hp, dvd_trans h (Nat.dvd_lcm_right _ _), Nat.lcm_ne_zero h1 h2⟩
  rw [hpf]
  simp only [hsq1, hsq2, hsqL, true_and, Finset.forall_mem_union]

/-- Page 15, the local count behind Ramare and Ruzsa reference 18 formula 4.1.13. For L
dividing P of z, every prime of L is above w, hence prime to W, so by the Chinese
remainder theorem exactly L times g of L residues t mod L have W t + b in A_L, with one residue at p
equal to 1 mod 4 and two at p equal to 3 mod 4. -/
theorem efs_count_period {J w : ℕ} (hw : 5 ≤ w) (b : ℤ) (z : ℝ) {L : ℕ}
    (hL : L ∣ envelopingPrimeProduct w z) :
    ∑ r ∈ range L, (if EnvelopingSifted w L (WW J w * (r : ℤ) + b) then (1 : ℝ) else 0) =
      (L : ℝ) * envelopingDensity w L := by
  induction L using Nat.strong_induction_on with
  | _ L ih =>
  have hP := envelopingPrimeProduct_ne_zero w z
  have hL0 : L ≠ 0 := fun h => hP (Nat.eq_zero_of_zero_dvd (h ▸ hL))
  by_cases hL1 : L = 1
  · subst hL1
    simp [EnvelopingSifted, envelopingDensity]
  obtain ⟨p, hp, hpL⟩ := Nat.exists_prime_and_dvd hL1
  obtain ⟨L', hL'⟩ := hpL
  have hsqL := (enveloping_divisor_support (J := J) hw hL).1
  rw [hL'] at hsqL
  have hcop : Nat.Coprime p L' := (Nat.squarefree_mul_iff.mp hsqL).1
  have hL'0 : L' ≠ 0 := by
    intro h; rw [h, mul_zero] at hL'; exact hL0 hL'
  have hL'lt : L' < L := by
    rw [hL']
    have := hp.two_le
    have : 0 < L' := Nat.pos_of_ne_zero hL'0
    nlinarith
  have hpP : p ∣ envelopingPrimeProduct w z := dvd_trans ⟨L', hL'⟩ hL
  have hL'P : L' ∣ envelopingPrimeProduct w z := dvd_trans ⟨p, by rw [hL']; ring⟩ hL
  have hwp : w < p := efs_prime_gt hp hpP
  have hpW : ¬ (p : ℤ) ∣ WW J w := by
    intro h
    rcases prime_dvd_Wmod (fun r hr => (Sw_spec w r hr).1) hp h with h | h | h
    · omega
    · omega
    · have := (mem_filter.mp h).1
      rw [mem_Icc] at this
      omega
  have hsplit : ∀ r : ℕ,
      (if EnvelopingSifted w L (WW J w * (r : ℤ) + b) then (1 : ℝ) else 0) =
        (if EnvelopingSifted w p (WW J w * ((r % p : ℕ) : ℤ) + b) then (1 : ℝ) else 0) *
        (if EnvelopingSifted w L' (WW J w * ((r % L' : ℕ) : ℤ) + b) then (1 : ℝ) else 0) := by
    intro r
    have e1 := efs_sifted_shift w p (WW J w) b p (r % p) (r / p) dvd_rfl
    have e2 := efs_sifted_shift w L' (WW J w) b L' (r % L') (r / L') dvd_rfl
    rw [Nat.div_add_mod] at e1 e2
    have e3 := efs_sifted_lcm hw hpP hL'P (WW J w * (r : ℤ) + b)
    rw [Nat.Coprime.lcm_eq_mul hcop, ← hL'] at e3
    rw [← e1, ← e2, ← e3]
    split_ifs <;> simp_all
  rw [sum_congr rfl (fun r _ => hsplit r), hL',
    efs_crt_sum p L' hp.pos (Nat.pos_of_ne_zero hL'0) hcop
      (fun x => if EnvelopingSifted w p (WW J w * (x : ℤ) + b) then (1 : ℝ) else 0)
      (fun y => if EnvelopingSifted w L' (WW J w * (y : ℤ) + b) then (1 : ℝ) else 0),
    ih L' hL'lt hL'P]
  have hsp : ∀ m : ℤ, EnvelopingSifted w p m ↔
      ((p : ℤ) ∣ m ∨ (p % 4 = 3 ∧ (p : ℤ) ∣ m - 1)) := by
    intro m
    unfold EnvelopingSifted
    rw [hp.primeFactors]
    simp [hp.squarefree, hwp]
  simp only [hsp]
  have hcount := efs_count_prime (WW J w) b p hp hpW (p % 4 = 3)
  have hdens : envelopingDensity w (p * L') = envelopingDensity w p * envelopingDensity w L' := by
    unfold envelopingDensity
    rw [Nat.Coprime.primeFactors_mul hcop,
      prod_union (Nat.Coprime.disjoint_primeFactors hcop)]
  have hdp : (p : ℝ) * envelopingDensity w p = if p % 4 = 3 then 2 else 1 := by
    unfold envelopingDensity
    rw [hp.primeFactors, prod_singleton]
    have hpr : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hodd : p % 2 = 1 := by
      rcases hp.eq_two_or_odd with h | h
      · omega
      · exact h
    unfold envelopingOmega
    rw [if_neg (by omega)]
    by_cases h3 : p % 4 = 3
    · rw [if_pos h3, if_neg (by omega)]
      field_simp
      norm_num
    · rw [if_neg h3, if_pos (by omega)]
      field_simp
      norm_num
  calc _ = (if p % 4 = 3 then (2 : ℝ) else 1) * ((L' : ℝ) * envelopingDensity w L') := by
        congr 1
        convert hcount
    _ = _ := by
        rw [hdens, ← hdp]
        push_cast
        ring

/-- Page 15 to 16, the local count behind Ramare and Ruzsa reference 18 formula 4.1.13:
the number of t mod P with W t + b in A_d1 and in A_d2 is P times g of lcm d1 d2, proved
from the periodicity of A of lcm d1 d2 and the count over one period. -/
theorem efs_count_lcm {J w : ℕ} (hw : 5 ≤ w) (b : ℤ) (z : ℝ) {d1 d2 : ℕ}
    (hd1 : d1 ∣ envelopingPrimeProduct w z) (hd2 : d2 ∣ envelopingPrimeProduct w z) :
    ∑ s ∈ range (envelopingPrimeProduct w z),
      ((if EnvelopingSifted w d1 (WW J w * (s : ℤ) + b) then (1 : ℝ) else 0) *
        (if EnvelopingSifted w d2 (WW J w * (s : ℤ) + b) then (1 : ℝ) else 0)) =
      (envelopingPrimeProduct w z : ℝ) * envelopingDensity w (Nat.lcm d1 d2) := by
  have hLP : Nat.lcm d1 d2 ∣ envelopingPrimeProduct w z := Nat.lcm_dvd hd1 hd2
  have hc := efs_count_period (J := J) hw b z hLP
  have hone : ∀ s : ℕ,
      ((if EnvelopingSifted w d1 (WW J w * (s : ℤ) + b) then (1 : ℝ) else 0) *
        (if EnvelopingSifted w d2 (WW J w * (s : ℤ) + b) then (1 : ℝ) else 0)) =
      (if EnvelopingSifted w (Nat.lcm d1 d2) (WW J w * (s : ℤ) + b) then (1 : ℝ) else 0) := by
    intro s
    rw [← efs_sifted_lcm hw hd1 hd2]
    split_ifs <;> simp_all
  rw [sum_congr rfl (fun s _ => hone s)]
  obtain ⟨m, hm⟩ := hLP
  rw [hm, efs_sum_range_mul]
  have hper : ∀ j r : ℕ,
      (if EnvelopingSifted w (Nat.lcm d1 d2) (WW J w * ((Nat.lcm d1 d2 * j + r : ℕ) : ℤ) + b)
        then (1 : ℝ) else 0) =
      (if EnvelopingSifted w (Nat.lcm d1 d2) (WW J w * (r : ℤ) + b) then (1 : ℝ) else 0) := by
    intro j r
    simp only [efs_sifted_shift w (Nat.lcm d1 d2) (WW J w) b (Nat.lcm d1 d2) r j dvd_rfl]
  rw [sum_congr rfl (fun j _ => sum_congr rfl (fun r _ => hper j r)), sum_const, card_range,
    nsmul_eq_mul, hc]
  push_cast
  ring

private theorem sel_mu_sq (w : ℕ) (hw : 5 ≤ w) (z : ℝ) {f : ℕ}
    (hf : f ∈ (envelopingPrimeProduct w z).divisors) :
    (ArithmeticFunction.moebius f : ℝ) ^ 2 = 1 := by
  have hsq := (enveloping_divisor_support (J := 5) hw (Nat.dvd_of_mem_divisors hf)).1
  rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]
  push_cast
  rw [← pow_mul, mul_comm, pow_mul]
  simp

private theorem sel_h_ne (w : ℕ) (hw : 5 ≤ w) (z : ℝ) {f : ℕ}
    (hf : f ∈ (envelopingPrimeProduct w z).divisors) : envelopingH w f ≠ 0 := by
  have hfP := Nat.dvd_of_mem_divisors hf
  have hsq := (enveloping_divisor_support (J := 5) hw hfP).1
  unfold envelopingH
  rw [if_pos hsq, prod_ne_zero_iff]
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hwp : w < p := efs_prime_gt hpp (dvd_trans (Nat.dvd_of_mem_primeFactors hp) hfP)
  unfold envelopingOmega
  rw [if_neg (by omega)]
  split_ifs
  · apply div_ne_zero (by norm_num)
    exact Nat.cast_ne_zero.mpr (by omega)
  · apply div_ne_zero (by norm_num)
    exact Nat.cast_ne_zero.mpr (by omega)

private theorem sel_h_dvd (w : ℕ) {z : ℝ} {δ : ℕ} (hδz : (δ : ℝ) ≤ z) (hh : envelopingH w δ ≠ 0) :
    δ ∣ envelopingPrimeProduct w z := by
  unfold envelopingH at hh
  split_ifs at hh with hsq
  · rw [prod_ne_zero_iff] at hh
    rw [← Nat.prod_primeFactors_of_squarefree hsq, envelopingPrimeProduct]
    apply prod_dvd_prod_of_subset
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hδ0 : δ ≠ 0 := (Nat.mem_primeFactors.mp hp).2.2
    have hpd' : p ≤ δ := Nat.le_of_dvd (Nat.pos_of_ne_zero hδ0) (Nat.dvd_of_mem_primeFactors hp)
    have hpz : (p : ℝ) ≤ z := le_trans (by exact_mod_cast hpd') hδz
    have hwp : w < p := by
      by_contra hc
      apply hh p hp
      simp [envelopingOmega, show p ≤ w by omega]
    refine mem_filter.mpr ⟨mem_range.mpr ?_, hpp, hwp, hpz⟩
    have := Nat.le_floor hpz
    omega
  · exact absurd rfl hh

private theorem sel_G1 (w : ℕ) (hw : 5 ≤ w) (z : ℝ) (hz : 1 ≤ z) :
    envelopingG w 1 z =
      ∑ e ∈ (envelopingPrimeProduct w z).divisors,
        (if (e : ℝ) ≤ z then envelopingH w e else 0) := by
  rw [← sum_filter]
  unfold envelopingG
  symm
  apply sum_subset
  · intro e he
    obtain ⟨he1, he2⟩ := mem_filter.mp he
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_mem_divisors he1, Nat.le_floor he2⟩, ?_⟩
    simpa using he2
  · intro δ hδ hδn
    obtain ⟨-, hδz⟩ := mem_filter.mp hδ
    simp only [Nat.lcm_one_left] at hδz
    by_contra hne
    apply hδn
    refine mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨sel_h_dvd w hδz hne,
      envelopingPrimeProduct_ne_zero w z⟩, hδz⟩

private theorem sel_sum_mu (k : ℕ) :
    ∑ j ∈ k.divisors, (ArithmeticFunction.moebius j : ℝ) = if k = 1 then 1 else 0 := by
  have h := congrArg (fun F : ArithmeticFunction ℤ => F k) ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  rw [← Int.cast_sum, h]
  split_ifs <;> simp

private theorem sel_moebius (w : ℕ) (hw : 5 ≤ w) (z : ℝ) {f e : ℕ}
    (hf : f ∈ (envelopingPrimeProduct w z).divisors)
    (he : e ∈ (envelopingPrimeProduct w z).divisors) :
    ∑ d ∈ (envelopingPrimeProduct w z).divisors,
      (if f ∣ d ∧ d ∣ e then (ArithmeticFunction.moebius d : ℝ) else 0) =
      if f = e then (ArithmeticFunction.moebius f : ℝ) else 0 := by
  have heP := Nat.dvd_of_mem_divisors he
  have hP := envelopingPrimeProduct_ne_zero w z
  have he0 : e ≠ 0 := fun h => hP (Nat.eq_zero_of_zero_dvd (h ▸ heP))
  have hsq := (enveloping_divisor_support (J := 5) hw heP).1
  by_cases hfe : f ∣ e
  · obtain ⟨k, rfl⟩ := hfe
    have hf0 : f ≠ 0 := left_ne_zero_of_mul he0
    have hk0 : k ≠ 0 := right_ne_zero_of_mul he0
    have hcop : Nat.Coprime f k := Nat.coprime_of_squarefree_mul hsq
    rw [← sum_filter]
    have hset : (envelopingPrimeProduct w z).divisors.filter (fun d => f ∣ d ∧ d ∣ f * k) =
        k.divisors.image (fun j => f * j) := by
      ext d
      simp only [mem_filter, Nat.mem_divisors, mem_image]
      constructor
      · rintro ⟨-, ⟨j, rfl⟩, hd⟩
        exact ⟨j, ⟨(Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hf0)).mp hd, hk0⟩, rfl⟩
      · rintro ⟨j, ⟨hj, -⟩, rfl⟩
        refine ⟨⟨dvd_trans (mul_dvd_mul_left f hj) heP, hP⟩, dvd_mul_right _ _,
          mul_dvd_mul_left f hj⟩
    rw [hset, sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hf0) h)]
    have hmul : ∀ j ∈ k.divisors, (ArithmeticFunction.moebius (f * j) : ℝ) =
        (ArithmeticFunction.moebius f : ℝ) * ArithmeticFunction.moebius j := by
      intro j hj
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
        (Nat.Coprime.coprime_dvd_right (Nat.dvd_of_mem_divisors hj) hcop)]
      push_cast; ring
    rw [sum_congr rfl hmul, ← mul_sum, sel_sum_mu]
    by_cases hk1 : k = 1
    · subst hk1; simp
    · have : f ≠ f * k := by
        intro h
        apply hk1
        have := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hf0) (h.symm.trans (mul_one f).symm)
        exact this
      simp [hk1, this]
  · have hne : f ≠ e := fun h => hfe (h ▸ dvd_rfl)
    rw [if_neg hne]
    apply sum_eq_zero
    intro d _
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hfe (dvd_trans h1 h2)

private theorem sel_divisors_image {n : ℕ} (hn : Squarefree n) :
    n.divisors = n.primeFactors.powerset.image (fun t => ∏ p ∈ t, p) := by
  have hn0 : n ≠ 0 := hn.ne_zero
  ext d
  simp only [Nat.mem_divisors, mem_image, mem_powerset]
  constructor
  · rintro ⟨hd, -⟩
    refine ⟨d.primeFactors, Nat.primeFactors_mono hd hn0, ?_⟩
    exact Nat.prod_primeFactors_of_squarefree (hn.squarefree_of_dvd hd)
  · rintro ⟨t, ht, rfl⟩
    refine ⟨?_, hn0⟩
    calc ∏ p ∈ t, p ∣ ∏ p ∈ n.primeFactors, p := prod_dvd_prod_of_subset _ _ _ ht
      _ = n := Nat.prod_primeFactors_of_squarefree hn

private theorem sel_sum_divisors {n : ℕ} (hn : Squarefree n) (F : ℕ → ℝ) :
    ∑ f ∈ n.divisors, F f = ∑ t ∈ n.primeFactors.powerset, F (∏ p ∈ t, p) := by
  rw [sel_divisors_image hn, sum_image]
  intro a ha b hb hab
  have hpa : ∀ p ∈ a, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (mem_powerset.mp ha hp)
  have hpb : ∀ p ∈ b, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (mem_powerset.mp hb hp)
  rw [← Nat.primeFactors_prod hpa, ← Nat.primeFactors_prod hpb]
  exact congrArg Nat.primeFactors hab

private theorem sel_h_prod (w : ℕ) {n : ℕ} (hn : Squarefree n) {t : Finset ℕ}
    (ht : t ⊆ n.primeFactors) :
    envelopingH w (∏ p ∈ t, p) =
      ∏ p ∈ t, (envelopingOmega w p : ℝ) / (p - envelopingOmega w p : ℕ) := by
  have hpt : ∀ p ∈ t, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (ht hp)
  have hdvd : ∏ p ∈ t, p ∣ n := by
    calc ∏ p ∈ t, p ∣ ∏ p ∈ n.primeFactors, p := prod_dvd_prod_of_subset _ _ _ ht
      _ = n := Nat.prod_primeFactors_of_squarefree hn
  unfold envelopingH
  rw [if_pos (hn.squarefree_of_dvd hdvd), Nat.primeFactors_prod hpt]

/-- 1 over g of n is the sum of 1 over h f over f dividing n, for n dividing P. -/
private theorem sel_inv_g (w : ℕ) (hw : 5 ≤ w) (z : ℝ) {n : ℕ}
    (hn : n ∣ envelopingPrimeProduct w z) :
    ∑ f ∈ n.divisors, (envelopingH w f)⁻¹ = (envelopingDensity w n)⁻¹ := by
  have hsq := (enveloping_divisor_support (J := 5) hw hn).1
  rw [sel_sum_divisors hsq]
  rw [sum_congr rfl (fun t ht => by rw [sel_h_prod w hsq (mem_powerset.mp ht), ← prod_inv_distrib])]
  rw [← prod_one_add, envelopingDensity, ← prod_inv_distrib]
  apply prod_congr rfl
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hwp : w < p := efs_prime_gt hpp (dvd_trans (Nat.dvd_of_mem_primeFactors hp) hn)
  unfold envelopingOmega
  rw [if_neg (by omega)]
  have hp6 : (6 : ℝ) ≤ p := by exact_mod_cast (show 6 ≤ p by omega)
  split_ifs
  · rw [Nat.cast_sub (by omega)]
    field_simp
    push_cast
    ring_nf
  · rw [Nat.cast_sub (by omega)]
    field_simp
    push_cast
    ring_nf


private theorem sel_g_ne (w : ℕ) (z : ℝ) {n : ℕ} (hn : n ∣ envelopingPrimeProduct w z) :
    envelopingDensity w n ≠ 0 := by
  unfold envelopingDensity
  rw [prod_ne_zero_iff]
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hwp : w < p := efs_prime_gt hpp (dvd_trans (Nat.dvd_of_mem_primeFactors hp) hn)
  unfold envelopingOmega
  rw [if_neg (by omega)]
  have : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpp.ne_zero
  split_ifs <;> simp [this]

private theorem sel_g_lcm (w : ℕ) (hw : 5 ≤ w) (z : ℝ) {d1 d2 : ℕ}
    (hd1 : d1 ∈ (envelopingPrimeProduct w z).divisors)
    (hd2 : d2 ∈ (envelopingPrimeProduct w z).divisors) :
    envelopingDensity w (Nat.lcm d1 d2) =
      envelopingDensity w d1 * envelopingDensity w d2 *
        ∑ f ∈ (envelopingPrimeProduct w z).divisors,
          (if f ∣ d1 then (1 : ℝ) else 0) * (if f ∣ d2 then (1 : ℝ) else 0) / envelopingH w f := by
  have hP := envelopingPrimeProduct_ne_zero w z
  have hd1P := Nat.dvd_of_mem_divisors hd1
  have hd2P := Nat.dvd_of_mem_divisors hd2
  have h1 : d1 ≠ 0 := fun h => hP (Nat.eq_zero_of_zero_dvd (h ▸ hd1P))
  have h2 : d2 ≠ 0 := fun h => hP (Nat.eq_zero_of_zero_dvd (h ▸ hd2P))
  have hgP : Nat.gcd d1 d2 ∣ envelopingPrimeProduct w z := dvd_trans (Nat.gcd_dvd_left _ _) hd1P
  have hsum : ∑ f ∈ (envelopingPrimeProduct w z).divisors,
      (if f ∣ d1 then (1 : ℝ) else 0) * (if f ∣ d2 then (1 : ℝ) else 0) / envelopingH w f =
      (envelopingDensity w (Nat.gcd d1 d2))⁻¹ := by
    rw [← sel_inv_g w hw z hgP]
    have hc : ∀ f ∈ (envelopingPrimeProduct w z).divisors,
        (if f ∣ d1 then (1 : ℝ) else 0) * (if f ∣ d2 then (1 : ℝ) else 0) / envelopingH w f =
        if f ∣ Nat.gcd d1 d2 then (envelopingH w f)⁻¹ else 0 := by
      intro f _
      simp only [Nat.dvd_gcd_iff]
      by_cases a : f ∣ d1 <;> by_cases b : f ∣ d2 <;> simp [a, b]
    rw [sum_congr rfl hc, ← sum_filter]
    apply sum_congr _ (fun _ _ => rfl)
    ext f
    simp only [mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨-, h⟩
      exact ⟨h, Nat.gcd_ne_zero_left h1⟩
    · rintro ⟨h, -⟩
      exact ⟨⟨dvd_trans h hgP, hP⟩, h⟩
  have hpf : (Nat.lcm d1 d2).primeFactors = (d1 * d2).primeFactors := by
    rw [Nat.primeFactors_mul h1 h2]
    ext p
    simp only [Finset.mem_union, Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp, hpd, -⟩
      rcases (Nat.Prime.dvd_mul hp).mp (dvd_trans hpd (Nat.lcm_dvd_mul d1 d2)) with h | h
      · exact Or.inl ⟨hp, h, h1⟩
      · exact Or.inr ⟨hp, h, h2⟩
    · rintro (⟨hp, h, -⟩ | ⟨hp, h, -⟩)
      · exact ⟨hp, dvd_trans h (Nat.dvd_lcm_left _ _), Nat.lcm_ne_zero h1 h2⟩
      · exact ⟨hp, dvd_trans h (Nat.dvd_lcm_right _ _), Nat.lcm_ne_zero h1 h2⟩
  have hmain : envelopingDensity w (Nat.gcd d1 d2) * envelopingDensity w (Nat.lcm d1 d2) =
      envelopingDensity w d1 * envelopingDensity w d2 := by
    unfold envelopingDensity
    rw [hpf]
    exact Nat.prod_primeFactors_gcd_mul_prod_primeFactors_mul d1 d2 _
  rw [hsum, ← hmain]
  have := sel_g_ne w z hgP
  field_simp

private theorem sel_pf_lcm {a b : ℕ} (h1 : a ≠ 0) (h2 : b ≠ 0) :
    (Nat.lcm a b).primeFactors = a.primeFactors ∪ b.primeFactors := by
  ext p
  simp only [Finset.mem_union, Nat.mem_primeFactors]
  constructor
  · rintro ⟨hp, hpd, -⟩
    rcases (Nat.Prime.dvd_mul hp).mp (dvd_trans hpd (Nat.lcm_dvd_mul a b)) with h | h
    · exact Or.inl ⟨hp, h, h1⟩
    · exact Or.inr ⟨hp, h, h2⟩
  · rintro (⟨hp, h, -⟩ | ⟨hp, h, -⟩)
    · exact ⟨hp, dvd_trans h (Nat.dvd_lcm_left _ _), Nat.lcm_ne_zero h1 h2⟩
    · exact ⟨hp, dvd_trans h (Nat.dvd_lcm_right _ _), Nat.lcm_ne_zero h1 h2⟩

private theorem sel_local (w : ℕ) (hw : 5 ≤ w) (z : ℝ) {p : ℕ} (hp : p.Prime)
    (hpP : p ∣ envelopingPrimeProduct w z) :
    (envelopingOmega w p : ℝ) / p *
      ((envelopingOmega w p : ℝ) / (p - envelopingOmega w p : ℕ) + 1) =
      (envelopingOmega w p : ℝ) / (p - envelopingOmega w p : ℕ) := by
  have hwp : w < p := efs_prime_gt hp hpP
  unfold envelopingOmega
  rw [if_neg (by omega)]
  have hp6 : (6 : ℝ) ≤ p := by exact_mod_cast (show 6 ≤ p by omega)
  split_ifs
  · rw [Nat.cast_sub (by omega)]
    have : (p : ℝ) - 1 ≠ 0 := by linarith
    push_cast
    field_simp
    ring
  · rw [Nat.cast_sub (by omega)]
    have : (p : ℝ) - 2 ≠ 0 := by linarith
    push_cast
    field_simp
    ring

/-- Page 15, the fibre of delta to lcm d delta over e carries mass h e over g d. -/
private theorem sel_K (w : ℕ) (hw : 5 ≤ w) (z : ℝ) {d e : ℕ} (hde : d ∣ e)
    (he : e ∣ envelopingPrimeProduct w z) :
    envelopingDensity w d *
      ∑ δ ∈ (envelopingPrimeProduct w z).divisors,
        (if Nat.lcm d δ = e then envelopingH w δ else 0) = envelopingH w e := by
  have hP := envelopingPrimeProduct_ne_zero w z
  have he0 : e ≠ 0 := fun h => hP (Nat.eq_zero_of_zero_dvd (h ▸ he))
  have hd0 : d ≠ 0 := fun h => he0 (Nat.eq_zero_of_zero_dvd (h ▸ hde))
  have hsq := (enveloping_divisor_support (J := 5) hw he).1
  set E := e.primeFactors with hE
  set Dp := d.primeFactors with hDp
  have hDE : Dp ⊆ E := Nat.primeFactors_mono hde he0
  set hp : ℕ → ℝ := fun p =>
    (envelopingOmega w p : ℝ) / (p - envelopingOmega w p : ℕ) with hhp
  -- step a
  have ha : ∑ δ ∈ (envelopingPrimeProduct w z).divisors,
      (if Nat.lcm d δ = e then envelopingH w δ else 0) =
      ∑ δ ∈ e.divisors, (if Nat.lcm d δ = e then envelopingH w δ else 0) := by
    symm
    apply sum_subset
    · intro δ hδ
      exact Nat.mem_divisors.mpr ⟨dvd_trans (Nat.dvd_of_mem_divisors hδ) he, hP⟩
    · intro δ _ hδ
      rw [if_neg]
      intro hl
      apply hδ
      exact Nat.mem_divisors.mpr ⟨hl ▸ Nat.dvd_lcm_right d δ, he0⟩
  -- steps b and c
  have hc : ∀ t ∈ E.powerset,
      (if Nat.lcm d (∏ p ∈ t, p) = e then envelopingH w (∏ p ∈ t, p) else 0) =
      (∏ p ∈ t, hp p) * ∏ p ∈ E \ t, (if p ∈ Dp then (1 : ℝ) else 0) := by
    intro t ht
    have htE : t ⊆ E := mem_powerset.mp ht
    have hpt : ∀ p ∈ t, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (htE hp)
    have htdvd : ∏ p ∈ t, p ∣ e := by
      calc ∏ p ∈ t, p ∣ ∏ p ∈ e.primeFactors, p := prod_dvd_prod_of_subset _ _ _ htE
        _ = e := Nat.prod_primeFactors_of_squarefree hsq
    have ht0 : ∏ p ∈ t, p ≠ 0 := fun h => he0 (Nat.eq_zero_of_zero_dvd (h ▸ htdvd))
    have hiff : Nat.lcm d (∏ p ∈ t, p) = e ↔ E \ t ⊆ Dp := by
      have hpf := sel_pf_lcm hd0 ht0
      rw [Nat.primeFactors_prod hpt] at hpf
      constructor
      · intro hl q hq
        rw [mem_sdiff] at hq
        have : q ∈ (Nat.lcm d (∏ p ∈ t, p)).primeFactors := by rw [hl]; exact hq.1
        rw [hpf, mem_union] at this
        rcases this with h | h
        · exact h
        · exact absurd h hq.2
      · intro hsub
        have hl : Nat.lcm d (∏ p ∈ t, p) ∣ e := Nat.lcm_dvd hde htdvd
        have hlsq := hsq.squarefree_of_dvd hl
        rw [← Nat.prod_primeFactors_of_squarefree hlsq, ← Nat.prod_primeFactors_of_squarefree hsq,
          hpf]
        congr 1
        ext q
        rw [mem_union]
        constructor
        · rintro (h | h)
          · exact hDE h
          · exact htE h
        · intro hq
          by_cases hqt : q ∈ t
          · exact Or.inr hqt
          · exact Or.inl (hsub (mem_sdiff.mpr ⟨hq, hqt⟩))
    have hbool : ∏ p ∈ E \ t, (if p ∈ Dp then (1 : ℝ) else 0) =
        if E \ t ⊆ Dp then 1 else 0 := by
      split_ifs with hs
      · exact prod_eq_one (fun p hp => if_pos (hs hp))
      · rw [not_subset] at hs
        obtain ⟨q, hq, hqD⟩ := hs
        exact prod_eq_zero hq (if_neg hqD)
    rw [hbool, sel_h_prod w hsq htE]
    by_cases hs : E \ t ⊆ Dp
    · rw [if_pos (hiff.mpr hs), if_pos hs, mul_one]
    · rw [if_neg (fun h => hs (hiff.mp h)), if_neg hs, mul_zero]
  rw [ha, sel_sum_divisors hsq, sum_congr rfl hc, ← prod_add]
  -- step e
  have hsplit : ∀ F : ℕ → ℝ, ∏ p ∈ E, F p = (∏ p ∈ Dp, F p) * ∏ p ∈ E.filter (· ∉ Dp), F p := by
    intro F
    rw [← prod_filter_mul_prod_filter_not E (· ∈ Dp)]
    congr 2
    ext q
    simp only [mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hDE h, h⟩⟩
  have hhe : envelopingH w e = ∏ p ∈ E, hp p := by
    unfold envelopingH; rw [if_pos hsq]
  rw [hhe, hsplit, hsplit hp]
  have h1 : ∏ p ∈ E.filter (· ∉ Dp), (hp p + if p ∈ Dp then (1 : ℝ) else 0) =
      ∏ p ∈ E.filter (· ∉ Dp), hp p :=
    prod_congr rfl (fun p hpm => by rw [if_neg (mem_filter.mp hpm).2, add_zero])
  have h2 : envelopingDensity w d * ∏ p ∈ Dp, (hp p + if p ∈ Dp then (1 : ℝ) else 0) =
      ∏ p ∈ Dp, hp p := by
    unfold envelopingDensity
    rw [← prod_mul_distrib]
    apply prod_congr rfl
    intro p hpD
    rw [if_pos hpD]
    exact sel_local w hw z (Nat.prime_of_mem_primeFactors hpD)
      (dvd_trans (dvd_trans (Nat.dvd_of_mem_primeFactors hpD) hde) he)
  rw [h1, ← mul_assoc, h2]


/-- Page 15 of P0076 and Ramare and Ruzsa reference 18 section 4.1, the lcm
reparametrization: for d dividing P of z, g of d times G_d of z is the sum of h of e over
the divisors e of P of z that are multiples of d and at most z. -/
private theorem sel_gG (w : ℕ) (hw : 5 ≤ w) (z : ℝ) (hz : 1 ≤ z) {d : ℕ}
    (hd : d ∈ (envelopingPrimeProduct w z).divisors) :
    envelopingDensity w d * envelopingG w d z =
      ∑ e ∈ (envelopingPrimeProduct w z).divisors,
        (if d ∣ e ∧ (e : ℝ) ≤ z then envelopingH w e else 0) := by
  have hP := envelopingPrimeProduct_ne_zero w z
  have hdP := Nat.dvd_of_mem_divisors hd
  set D := (envelopingPrimeProduct w z).divisors with hD
  have hGd : envelopingG w d z =
      ∑ δ ∈ D, (if (Nat.lcm d δ : ℝ) ≤ z then envelopingH w δ else 0) := by
    rw [← sum_filter]
    unfold envelopingG
    symm
    apply sum_subset
    · intro δ hδ
      obtain ⟨hδ1, hδ2⟩ := mem_filter.mp hδ
      have hδ0 : δ ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hδ1)
      have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
      have hδle : δ ≤ Nat.lcm d δ :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.lcm_ne_zero hd0 hδ0)) (Nat.dvd_lcm_right d δ)
      have hle : (δ : ℝ) ≤ z := le_trans (by exact_mod_cast hδle) hδ2
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hδ1, Nat.le_floor hle⟩, hδ2⟩
    · intro δ hδ hδn
      obtain ⟨hδI, hδz⟩ := mem_filter.mp hδ
      have hδ0 : δ ≠ 0 := by have := (mem_Icc.mp hδI).1; omega
      have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
      have hδle : δ ≤ Nat.lcm d δ :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.lcm_ne_zero hd0 hδ0)) (Nat.dvd_lcm_right d δ)
      have hle : (δ : ℝ) ≤ z := le_trans (by exact_mod_cast hδle) hδz
      by_contra hne
      exact hδn (mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨sel_h_dvd w hle hne, hP⟩, hδz⟩)
  have hR : ∀ e ∈ D, (if d ∣ e ∧ (e : ℝ) ≤ z then envelopingH w e else 0) =
      ∑ δ ∈ D, envelopingDensity w d *
        (if d ∣ e ∧ (e : ℝ) ≤ z then (if Nat.lcm d δ = e then envelopingH w δ else 0) else 0) := by
    intro e he
    split_ifs with h
    · rw [← mul_sum, sel_K w hw z h.1 (Nat.dvd_of_mem_divisors he)]
    · simp
  rw [sum_congr rfl hR, sum_comm, hGd, mul_sum]
  refine sum_congr rfl (fun δ hδ => ?_)
  rw [← mul_sum]
  congr 1
  have hlP : Nat.lcm d δ ∈ D :=
    Nat.mem_divisors.mpr ⟨Nat.lcm_dvd hdP (Nat.dvd_of_mem_divisors hδ), hP⟩
  have hx : ∀ e ∈ D, (if d ∣ e ∧ (e : ℝ) ≤ z then
      (if Nat.lcm d δ = e then envelopingH w δ else 0) else 0) =
      if Nat.lcm d δ = e then (if (Nat.lcm d δ : ℝ) ≤ z then envelopingH w δ else 0) else 0 := by
    intro e _
    by_cases hl : Nat.lcm d δ = e
    · subst hl
      simp [Nat.dvd_lcm_left]
    · simp [hl]
  rw [sum_congr rfl hx, sum_ite_eq D (Nat.lcm d δ), if_pos hlP]

/-- Page 17, the linear forms y_f of the diagonalized quadratic form. -/
private theorem sel_y (w : ℕ) (hw : 5 ≤ w) (z : ℝ) (hz : 1 ≤ z) {f : ℕ}
    (hf : f ∈ (envelopingPrimeProduct w z).divisors) :
    ∑ d ∈ (envelopingPrimeProduct w z).divisors,
      envelopingRho w d z * envelopingDensity w d * (if f ∣ d then (1 : ℝ) else 0) =
      if (f : ℝ) ≤ z then
        (ArithmeticFunction.moebius f : ℝ) * envelopingH w f / envelopingG w 1 z else 0 := by
  set D := (envelopingPrimeProduct w z).divisors
  set G := envelopingG w 1 z
  have step1 : ∀ d ∈ D,
      envelopingRho w d z * envelopingDensity w d * (if f ∣ d then (1 : ℝ) else 0) =
      ∑ e ∈ D, (if (e : ℝ) ≤ z then envelopingH w e else 0) / G *
        (if f ∣ d ∧ d ∣ e then (ArithmeticFunction.moebius d : ℝ) else 0) := by
    intro d hd
    have h1 : envelopingRho w d z * envelopingDensity w d =
        (ArithmeticFunction.moebius d : ℝ) / G *
          (envelopingDensity w d * envelopingG w d z) := by
      unfold envelopingRho; ring
    rw [h1, sel_gG w hw z hz hd, mul_sum, sum_mul]
    refine sum_congr rfl (fun e _ => ?_)
    by_cases hfd : f ∣ d <;> by_cases hde : d ∣ e <;> by_cases hez : (e : ℝ) ≤ z <;>
      simp [hfd, hde, hez]; ring
  rw [sum_congr rfl step1, sum_comm]
  simp_rw [← mul_sum]
  rw [sum_congr rfl (fun e he => by rw [sel_moebius w hw z hf he])]
  simp only [mul_ite, mul_zero]
  rw [sum_ite_eq D f]
  simp only [hf, ite_true]
  split_ifs <;> ring
private theorem sel_identity_assembly {w : ℕ} (hw : 5 ≤ w) {z : ℝ} (hz : 1 ≤ z) :
    envelopingG w 1 z *
      ∑ d1 ∈ (envelopingPrimeProduct w z).divisors, ∑ d2 ∈ (envelopingPrimeProduct w z).divisors,
        envelopingRho w d1 z * envelopingRho w d2 z * envelopingDensity w (Nat.lcm d1 d2) = 1 := by
  set D := (envelopingPrimeProduct w z).divisors with hD
  set G := envelopingG w 1 z with hGdef
  have hG : G ≠ 0 := (lt_of_lt_of_le one_pos (envelopingG_one_le w hz)).ne'
  set a : ℕ → ℕ → ℝ := fun d f =>
    envelopingRho w d z * envelopingDensity w d * (if f ∣ d then (1 : ℝ) else 0) with ha
  have hexp : ∀ d1 ∈ D, ∀ d2 ∈ D,
      envelopingRho w d1 z * envelopingRho w d2 z * envelopingDensity w (Nat.lcm d1 d2) =
      ∑ f ∈ D, a d1 f * a d2 f / envelopingH w f := by
    intro d1 hd1 d2 hd2
    rw [sel_g_lcm w hw z hd1 hd2, mul_sum, mul_sum]
    refine sum_congr rfl (fun f _ => ?_)
    simp only [ha]
    ring
  have hQ : ∑ d1 ∈ D, ∑ d2 ∈ D,
      envelopingRho w d1 z * envelopingRho w d2 z * envelopingDensity w (Nat.lcm d1 d2) =
      ∑ f ∈ D, (∑ d ∈ D, a d f) * (∑ d ∈ D, a d f) / envelopingH w f := by
    rw [sum_congr rfl (fun d1 hd1 => sum_congr rfl (fun d2 hd2 => hexp d1 hd1 d2 hd2))]
    conv_rhs => simp only [sum_mul_sum, sum_div]
    rw [sum_congr rfl (fun d1 _ => sum_comm)]
    rw [sum_comm]
  have hy : ∀ f ∈ D, (∑ d ∈ D, a d f) * (∑ d ∈ D, a d f) / envelopingH w f =
      (if (f : ℝ) ≤ z then envelopingH w f else 0) / G ^ 2 := by
    intro f hf
    have hyf : ∑ d ∈ D, a d f = _ := sel_y w hw z hz hf
    rw [← hGdef] at hyf
    rw [hyf]
    have hh := sel_h_ne w hw z hf
    have hmu := sel_mu_sq w hw z hf
    split_ifs
    · field_simp
      exact hmu
    · simp
  rw [hQ, sum_congr rfl hy, ← sum_div, ← sel_G1 w hw z hz]
  field_simp
  ring

/-- Proposition 4.1 v, page 17, the Selberg normalization. Putting q equal to 1 into
Ramare and Ruzsa reference 18 formula 4.1.15 gives w 1 sharp equal to 1 over G 1 of z, that
is, with rho_d as on page 15, G 1 of z times the Selberg quadratic form sum of rho_d1 rho_d2
g of lcm d1 d2 over d1 and d2 dividing P of z equals 1. The form is diagonalized: rho_d g d
is a linear form in f, Moebius inversion gives y_f equal to mu f times h f over G 1, and the
sum over f of y_f squared over h f is G 1 over G 1 squared. -/
theorem efs_selberg_identity {w : ℕ} (hw : 5 ≤ w) {z : ℝ} (hz : 1 ≤ z) :
    envelopingG w 1 z *
      ∑ d1 ∈ (envelopingPrimeProduct w z).divisors, ∑ d2 ∈ (envelopingPrimeProduct w z).divisors,
        envelopingRho w d1 z * envelopingRho w d2 z * envelopingDensity w (Nat.lcm d1 d2) = 1 := by
  exact sel_identity_assembly hw hz

/-- Proposition 4.1 v, page 17, the normalization v 1 equal to 1, proved from the local
count and the Selberg normalization leaves: the mean of display 4.3 over one period is
G 1 of z times the Selberg quadratic form. -/
theorem enveloping_vraw_one_zero {J w : ℕ} (hJ : 5 ≤ J) (hw : wBig ≤ w) {b : ℤ}
    (hb : 0 ≤ b) (hbW : b < WW J w) (hamen : Amenable (WW J w) b) {M : ℕ} (hM : 1 ≤ M) :
    envelopingVraw w (WW J w) b M 1 0 = 1 := by
  have hwBig : (5 : ℝ) ≤ wBig := by
    calc (5 : ℝ) ≤ 10 := by norm_num
      _ = (10 : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ wBig := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (Real.one_le_rpow (by norm_num) (by positivity))
  have hw5 : 5 ≤ w := by exact_mod_cast (hwBig.trans hw)
  have hz : (1 : ℝ) ≤ (M : ℝ) ^ ((1 : ℝ) / 10) :=
    Real.one_le_rpow (by exact_mod_cast hM) (by norm_num)
  have hR : ∑ s ∈ range (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))),
      envelopingF w (WW J w) b M s =
        (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10)) : ℝ) := by
    simp only [efs_F_expand]
    have hsel := efs_selberg_identity hw5 hz
    generalize (M : ℝ) ^ ((1 : ℝ) / 10) = z at hsel ⊢
    rw [sum_comm]
    have hterm : ∀ d1 ∈ (envelopingPrimeProduct w z).divisors,
        ∑ s ∈ range (envelopingPrimeProduct w z),
          ∑ d2 ∈ (envelopingPrimeProduct w z).divisors,
            envelopingG w 1 z *
              (if EnvelopingSifted w d1 (WW J w * (s : ℤ) + b) then envelopingRho w d1 z else 0) *
              (if EnvelopingSifted w d2 (WW J w * (s : ℤ) + b) then envelopingRho w d2 z else 0) =
        ∑ d2 ∈ (envelopingPrimeProduct w z).divisors,
          (envelopingPrimeProduct w z : ℝ) * (envelopingG w 1 z *
            (envelopingRho w d1 z * envelopingRho w d2 z *
              envelopingDensity w (Nat.lcm d1 d2))) := by
      intro d1 hd1
      rw [sum_comm]
      apply sum_congr rfl
      intro d2 hd2
      have hc := efs_count_lcm (J := J) hw5 b z (Nat.dvd_of_mem_divisors hd1)
        (Nat.dvd_of_mem_divisors hd2)
      calc _ = envelopingG w 1 z * envelopingRho w d1 z * envelopingRho w d2 z *
            ∑ s ∈ range (envelopingPrimeProduct w z),
              ((if EnvelopingSifted w d1 (WW J w * (s : ℤ) + b) then (1 : ℝ) else 0) *
                (if EnvelopingSifted w d2 (WW J w * (s : ℤ) + b) then (1 : ℝ) else 0)) := by
            rw [mul_sum]
            apply sum_congr rfl
            intro s _
            split_ifs <;> ring
        _ = _ := by rw [hc]; ring
    rw [sum_congr rfl hterm]
    conv_rhs => rw [← mul_one (envelopingPrimeProduct w z : ℝ), ← hsel]
    simp only [mul_sum]
  unfold envelopingVraw
  have he0 : ∀ s : ℕ, eC (((0 : ℕ) : ℝ) * s / ((1 : ℕ) : ℝ)) = 1 := by
    intro s
    simpa using efs_eC_int 0
  simp only [he0, mul_one]
  rw [← Complex.ofReal_sum, hR]
  have hP : (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10)) : ℂ) ≠ 0 := by
    exact_mod_cast envelopingPrimeProduct_ne_zero _ _
  push_cast
  field_simp

/-- LEAF: Proposition 4.1 v, page 16 after display 4.5, the decay bound v of a over q
at most a constant times q to the epsilon minus 1, class HARD. Cited: Ramare and Ruzsa
reference 18 formulas 4.1.13, 4.1.14, 4.1.15 and 4.1.17, via display 4.5, together with the
choice of the sets K_d in display 4.2 so that formula 4.1.18 of reference 18 holds with
xi equal to 2 epsilon. The constant depends on epsilon only. -/
theorem enveloping_v_decay :
    ∃ D : ℝ → ℝ, (∀ ε : ℝ, 0 < ε → 0 < D ε) ∧
      ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ,
        0 ≤ b → b < WW J w → Amenable (WW J w) b → ∀ M : ℕ, 1 ≤ M →
          ∀ ε : ℝ, 0 < ε → ∀ q : ℕ, 1 ≤ q → ∀ a < q, Nat.Coprime a q →
            ‖envelopingV w (WW J w) b M q a‖ ≤ D ε * (q : ℝ) ^ (ε - 1) := by
  sorry

/-- Assembly of Proposition 4.1 iv and v from the leaves above. -/
theorem paper_enveloping_fourier_decay_input_of_leaves :
    ∃ D : ℝ → ℝ, (∀ ε : ℝ, 0 < ε → 0 < D ε) ∧
      ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ,
        0 ≤ b → b < WW J w → Amenable (WW J w) b → ∀ M : ℕ, 1 ≤ M →
          EnvelopingFourierExpansion w (WW J w) b M D := by
  obtain ⟨D, hD, Hdecay⟩ := enveloping_v_decay
  refine ⟨D, hD, ?_⟩
  intro J w hJ hw b hb hbW hamen M hM
  have hwBig : (5 : ℝ) ≤ wBig := by
    calc (5 : ℝ) ≤ 10 := by norm_num
      _ = (10 : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ wBig := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (Real.one_le_rpow (by norm_num) (by positivity))
  have hw5 : 5 ≤ w := by exact_mod_cast (hwBig.trans hw)
  set P := envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10)) with hPdef
  have hP0 : P ≠ 0 := by
    rw [hPdef, envelopingPrimeProduct]
    exact prod_ne_zero_iff.mpr (fun p hp => (mem_filter.mp hp).2.1.ne_zero)
  refine ⟨envelopingV w (WW J w) b M, ?_, ?_, ?_, ?_⟩
  · rw [envelopingV, if_pos ⟨one_dvd _, squarefree_one, Nat.coprime_one_left _,
      Nat.zero_lt_one, Nat.coprime_zero_left 1 |>.mpr rfl⟩]
    exact enveloping_vraw_one_zero hJ hw hb hbW hamen hM
  · intro q a h hq1
    rw [envelopingV, if_neg]
    rintro ⟨_, hsq, hcop, _, _⟩
    rcases h with h | h
    · exact h hsq
    · exact hq1 (Nat.Coprime.eq_one_of_dvd hcop (Int.natCast_dvd.mp h))
  · intro ε hε q hq a ha hcop
    exact Hdecay J w hJ hw b hb hbW hamen M hM ε hε q hq a ha hcop
  · intro n _
    rw [envelopingBeta_eq_F, enveloping_fourier_inversion]
    set t := if n = 0 then M else n
    set N := ⌊(M : ℝ) ^ ((1 : ℝ) / 5)⌋₊
    let g : ℕ → ℂ := fun q => ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      envelopingVraw w (WW J w) b M q a * eC (-((a : ℝ) * t / q))
    let h : ℕ → ℂ := fun q => ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      envelopingV w (WW J w) b M q a * eC (-((a : ℝ) * t / q))
    change ∑ q ∈ P.divisors, g q = ∑ q ∈ Icc 1 N, h q
    have h1 : ∑ q ∈ P.divisors ∩ Icc 1 N, g q = ∑ q ∈ P.divisors, g q := by
      apply sum_subset inter_subset_left
      intro q hq hqn
      have hqP : q ∣ P := Nat.dvd_of_mem_divisors hq
      have hq1 : 1 ≤ q := Nat.pos_of_mem_divisors hq
      have hqN : N < q := by
        by_contra hc
        exact hqn (mem_inter.mpr ⟨hq, mem_Icc.mpr ⟨hq1, by omega⟩⟩)
      apply sum_eq_zero
      intro a ha
      rw [enveloping_vraw_vanish w (WW J w) b M q a hqP hqN (mem_filter.mp ha).2, zero_mul]
    have h2 : ∑ q ∈ P.divisors ∩ Icc 1 N, h q = ∑ q ∈ Icc 1 N, h q := by
      apply sum_subset inter_subset_right
      intro q hq hqn
      have hqP : ¬ q ∣ P := by
        intro hd
        exact hqn (mem_inter.mpr ⟨Nat.mem_divisors.mpr ⟨hd, hP0⟩, hq⟩)
      apply sum_eq_zero
      intro a _
      rw [envelopingV, if_neg (fun hh => hqP hh.1), zero_mul]
    rw [← h1, ← h2]
    apply sum_congr rfl
    intro q hq
    have hqP : q ∣ P := Nat.dvd_of_mem_divisors (mem_inter.mp hq).1
    obtain ⟨hsq, hcop⟩ := enveloping_divisor_support (J := J) hw5 hqP
    apply sum_congr rfl
    intro a ha
    have ha' := mem_filter.mp ha
    rw [envelopingV, if_pos ⟨hqP, hsq, hcop, mem_range.mp ha'.1, ha'.2⟩]

end LeanLab.Teravainen2016
