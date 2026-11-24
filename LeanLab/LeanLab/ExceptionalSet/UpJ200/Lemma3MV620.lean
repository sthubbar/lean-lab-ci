import LeanLab.ExceptionalSet.UpJ200.Lemma3MV617Integral
import LeanLab.ExceptionalSet.UpJ200.Lemma2MV.Lemma55KSum
import LeanLab.ExceptionalSet.UpJ200.Lemma2MV.Lemma55Termwise

/-!
# Split of the LEAF `mv_620` of `Lemma3MV617Integral`

Burst burst-20261122, step mv620, run by a Claude cloud session S112.

Source P0015, Montgomery and Vaughan 1975, display (6.20), page 365. MV evaluate
`Σ_{q ≥ 1, r̃ ∣ q} μ(q) τ(χ̃χ₀) c_{χ̃χ₀}(-n) φ(q)⁻²` by writing `q = r̃ m` with `(m, r̃) = 1`:
the twisted sum factors as `χ̃(-1) χ̃(n) χ̃(m) τ(χ̃) c_m(n)` because `χ̃` is primitive, so it
vanishes when `(n, r̃) > 1`; `τ(χ̃χ₀) = μ(m) χ̃(m) τ(χ̃)` and `τ(χ̃)² = χ̃(-1) r̃`. The term is then
`μ(r̃) χ̃(n) r̃ φ(r̃)⁻² μ(m)² c_m(-n) φ(m)⁻²`, and the `m` sum is the Euler product `∏ ∏ ≪ n φ(n)⁻¹`.

* PROVED `mv_620_termwise`: the termwise evaluation, stated as the bound by
  `|χ̃(n)|² r̃ φ(r̃)⁻² |μ(m)² c_m(-n) φ(m)⁻²|`, `m = q / r̃`, from the lab's proved Lemmas 5.1,
  5.2 and 5.4 of P0015 in `Lemma55Termwise`.
* PROVED `mv_620_main_abs`: `Σ_m |μ(m)² c_m(-n) φ(m)⁻²| ≪ n φ(n)⁻¹`, the absolute form of
  the Euler product bound in (6.20), from `Lemma2MVKSum.lem55_ksum_proved` at `r₄ = 1`.
* PROVED `mv_620_split` and its alias `mv_620_proved`, exact type twin of
  `Lemma3MV617Integral.mv_620`, sorry free.

A python check of the termwise bound and of the vanishing for `(n, r̃) > 1`, for `r̃` in
3, 4, 5, 7, 8, 12, `n < 40`, `m < 60`, found no violation.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Lemma3MV620

open Real Finset
open LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit (mainWeight mv_singular_series_616)
open LeanLab.ExceptionalSet.UpJ200.Lemma3MV617Integral

/-- P0015 page 360 and (6.20): `|μ(q)² c_q(-n) φ(q)⁻²| = μ(q)² φ(q)⁻¹ φ(q/(q,n))⁻¹`. PROVED. -/
theorem norm_mainWeight_eq_sqfree (q n : ℕ) : ‖mainWeight q n‖ = if Squarefree q then
      1 / (((q.totient : ℕ) : ℝ) * (((q / Nat.gcd q n).totient : ℕ) : ℝ)) else 0 := by
    rw [LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.norm_mainWeight_eq,
      LeanLab.HeathBrown1985.gm_eq]
    split_ifs with hsq
    · rw [LeanLab.ExceptionalSet.UpJ200.Lemma2MVKSum.ksum_term_eq hsq n, abs_prod]
      refine prod_congr rfl fun p hp => ?_
      have hpp := Nat.prime_of_mem_primeFactors hp
      have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
      unfold LeanLab.ExceptionalSet.UpJ200.Lemma2MVKSum.ksumW
      by_cases hd : p ∣ n
      · rw [LeanLab.HeathBrown1985.vloc_dvd hpp hd, if_pos hd, mul_one,
          abs_of_pos (by apply div_pos one_pos; linarith)]
      · rw [LeanLab.HeathBrown1985.vloc_not_dvd hpp hd, if_neg hd, abs_div, abs_neg, abs_one,
          abs_of_pos (by nlinarith), sq]
    · simp

/-- P0015 display (6.20), page 365, the termwise evaluation, PROVED via Lemmas 5.1 to 5.4: for `r̃ ∣ q`,
`q = r̃ m`, the term `μ(q) c_{χ̃χ₀}(-n) τ(χ̃χ₀) φ(q)⁻²` equals
`μ(r̃) χ̃(n) r̃ φ(r̃)⁻² μ(m)² c_m(-n) φ(m)⁻²` when `(m, r̃) = 1` and vanishes otherwise; stated
here as the bound of its absolute value by `|χ̃(n)|² r̃ φ(r̃)⁻² |μ(m)² c_m(-n) φ(m)⁻²|`. -/
theorem mv_620_termwise : ∀ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r),
    χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → ∀ n : ℕ, 1 ≤ n → ∀ q : ℕ, r ∣ q →
      ‖crossWeight χ q n‖ ≤
        ‖χ ((n : ℤ) : ZMod r)‖ ^ 2 * (r : ℝ) / (r.totient : ℝ) ^ 2 * ‖mainWeight (q / r) n‖ := by
  intro r hr χ hprim _ _ n hn q hrq
  have hRHS : 0 ≤ ‖χ ((n : ℤ) : ZMod r)‖ ^ 2 * (r : ℝ) / (r.totient : ℝ) ^ 2 *
      ‖mainWeight (q / r) n‖ := by positivity
  rcases Nat.eq_zero_or_pos q with hq0 | hqpos
  · subst hq0
    rw [crossWeight_of_tau χ n (tauInd_zero χ), norm_zero]; exact hRHS
  have hq1 : 1 ≤ q := hqpos
  have hq0 : q ≠ 0 := by omega
  have : NeZero q := ⟨hq0⟩
  have hr0 : r ≠ 0 := NeZero.ne r
  have hr1 : 1 ≤ r := Nat.pos_of_ne_zero hr0
  set ψ := DirichletCharacter.changeLevel hrq χ with hψ
  have htau : tauInd χ q = LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.rem66_cchi ψ 1 := by
    unfold tauInd
    rw [dif_pos ⟨hrq, hq0⟩, LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.rem66_cchi_one_eq_gaussSum]
  have hram : ramanujanInd χ q n =
      LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.rem66_cchi ψ (-(n : ℤ)) := by
    unfold ramanujanInd LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.rem66_cchi
    rw [dif_pos hrq]
    refine sum_congr rfl fun a _ => ?_
    congr 2
    push_cast
    ring
  by_cases hsqf : Squarefree q
  swap
  · have : crossWeight χ q n = 0 := by
      unfold crossWeight
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsqf]; simp
    rw [this, norm_zero]; exact hRHS
  -- the Gauss sum bound, Lemmas 5.1 and 5.2
  have hτ : ‖tauInd χ q‖ ≤ Real.sqrt r := by
    rw [htau, LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.mv_lemma52 r q χ hrq hq1 hprim,
      norm_mul, norm_mul]
    have h51 := LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.mv_lemma51_norm_le r χ hr1
    have h1 : ‖((ArithmeticFunction.moebius (q / r) : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have h2 : ‖χ ((q / r : ℕ) : ZMod r)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
    calc _ ≤ 1 * 1 * Real.sqrt r := by gcongr
      _ = _ := by ring
  have hcond : ψ.conductor = r := by
    rw [hψ, DirichletCharacter.conductor_changeLevel]; exact hprim
  have hc := LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.mv_cchi_bound
    LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.mv_lemma52 q ψ hq1 (-(n : ℤ))
  have hna : (-(n : ℤ)).natAbs = n := by simp
  rw [hna, hcond] at hc
  have hnorm : ‖crossWeight χ q n‖ =
      |((ArithmeticFunction.moebius q : ℤ) : ℝ)| * ‖ramanujanInd χ q n‖ * ‖tauInd χ q‖ /
        (q.totient : ℝ) ^ 2 := by
    unfold crossWeight
    rw [norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_intCast]
  have hmu : |((ArithmeticFunction.moebius q : ℤ) : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  set g := Nat.gcd q n with hg
  by_cases hdv : r ∣ q / g
  swap
  · rw [if_neg hdv, ← hram] at hc
    have : ‖ramanujanInd χ q n‖ = 0 := le_antisymm hc (norm_nonneg _)
    rw [hnorm, this]; simp only [mul_zero, zero_mul, zero_div]; exact hRHS
  rw [if_pos hdv, ← hram] at hc
  -- the arithmetic: `q = r m`, `(m, r) = 1`, `(n, r) = 1`, `g = (m, n)`
  obtain ⟨m, rfl⟩ := hrq
  have hm : r * m / r = m := Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hr0)
  rw [hm]
  have hsq2 := Nat.squarefree_mul_iff.mp hsqf
  have hrm : Nat.Coprime r m := hsq2.1
  have hm0 : m ≠ 0 := by rintro rfl; simp at hq0
  have hgq : g ∣ r * m := Nat.gcd_dvd_left _ _
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ hqpos
  have hsplit : g * (r * m / g) = r * m := Nat.mul_div_cancel' hgq
  have hcop1 : Nat.Coprime g (r * m / g) := by
    have : Squarefree (g * (r * m / g)) := by rw [hsplit]; exact hsqf
    exact (Nat.squarefree_mul_iff.mp this).1
  have hgr : Nat.Coprime g r := Nat.Coprime.coprime_dvd_right hdv hcop1
  have hnr : Nat.Coprime r n := by
    have h1 : Nat.gcd r n ∣ g := Nat.dvd_gcd ((Nat.gcd_dvd_left r n).trans (dvd_mul_right r m))
      (Nat.gcd_dvd_right r n)
    have h2 : Nat.gcd r n ∣ Nat.gcd g r := Nat.dvd_gcd h1 (Nat.gcd_dvd_left r n)
    rw [hgr] at h2
    exact Nat.eq_one_of_dvd_one h2
  have hgm : g = Nat.gcd m n := by rw [hg]; exact Nat.Coprime.gcd_mul_left_cancel m hnr
  have hgdm : g ∣ m := by rw [hgm]; exact Nat.gcd_dvd_left m n
  have hqg : r * m / g = r * (m / g) := Nat.mul_div_assoc r hgdm
  have hrmg : Nat.Coprime r (m / g) := Nat.Coprime.coprime_div_right hrm hgdm
  have hphi1 : ((r * m).totient : ℝ) = (r.totient : ℝ) * (m.totient : ℝ) := by
    rw [Nat.totient_mul hrm]; push_cast; ring
  have hphi2 : ((r * m / g).totient : ℝ) = (r.totient : ℝ) * ((m / g).totient : ℝ) := by
    rw [hqg, Nat.totient_mul hrmg]; push_cast; ring
  have hchi : ‖χ ((n : ℤ) : ZMod r)‖ = 1 := by
    have hu : IsUnit ((n : ℕ) : ZMod r) := (ZMod.isUnit_iff_coprime n r).mpr hnr.symm
    have := DirichletCharacter.unit_norm_eq_one χ hu.unit
    rw [IsUnit.unit_spec] at this
    rw [Int.cast_natCast]; exact this
  have hmw : ‖mainWeight m n‖ =
      1 / (((m.totient : ℕ) : ℝ) * (((m / g).totient : ℕ) : ℝ)) := by
    rw [norm_mainWeight_eq_sqfree, if_pos hsq2.2.2, hgm]
  rw [hchi, hmw, hnorm]
  have hpr : (0 : ℝ) < r.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hpm : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hmg : 0 < m / g := Nat.div_pos (Nat.le_of_dvd (by omega) hgdm) hgpos
  have hpmg : (0 : ℝ) < (m / g).totient := by exact_mod_cast Nat.totient_pos.mpr hmg
  have hpq : (0 : ℝ) < (r * m).totient := by rw [hphi1]; positivity
  have hsr : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt (Nat.cast_nonneg r)
  rw [hphi2] at hc
  calc |((ArithmeticFunction.moebius (r * m) : ℤ) : ℝ)| * ‖ramanujanInd χ (r * m) n‖ *
        ‖tauInd χ (r * m)‖ / ((r * m).totient : ℝ) ^ 2
      ≤ 1 * (Real.sqrt r * (((r * m).totient : ℝ) / ((r.totient : ℝ) * ((m / g).totient : ℝ)))) *
          Real.sqrt r / ((r * m).totient : ℝ) ^ 2 := by gcongr
    _ = 1 ^ 2 * (r : ℝ) / (r.totient : ℝ) ^ 2 *
          (1 / (((m.totient : ℕ) : ℝ) * (((m / g).totient : ℕ) : ℝ))) := by
        rw [hphi1]
        generalize Real.sqrt (r : ℝ) = t at hsr ⊢
        rw [← hsr]
        field_simp

/-- P0015 display (6.20), page 365, the Euler product bound, PROVED via `lem55_ksum_proved`:
`Σ_{m ≥ 1} μ(m)² |c_m(-n)| φ(m)⁻² ≤ ∏_{p ∤ n} (1 + (p-1)⁻²) ∏_{p ∣ n} (1 + (p-1)⁻¹) ≪ n φ(n)⁻¹`. -/
theorem mv_620_main_abs : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
    ∑' m : ℕ, ‖mainWeight m n‖ ≤ C * ((n : ℝ) / (n.totient : ℝ)) := by
  obtain ⟨C, hC, hK⟩ := LeanLab.ExceptionalSet.UpJ200.Lemma2MVKSum.lem55_ksum_proved
  refine ⟨C, hC, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by omega
  have hterm := fun q => norm_mainWeight_eq_sqfree q n
  have hnn : ∀ q : ℕ, 0 ≤ ‖mainWeight q n‖ := fun q => norm_nonneg _
  have hprod : ∏ p ∈ (n : ℤ).natAbs.primeFactors.filter (fun p => ¬ p ∣ 1),
      (1 - 1 / (p : ℝ))⁻¹ = (n : ℝ) / (n.totient : ℝ) := by
    have hf : (n : ℤ).natAbs.primeFactors.filter (fun p => ¬ p ∣ 1) = n.primeFactors := by
      rw [Int.natAbs_natCast]
      refine filter_true_of_mem fun p hp => ?_
      rw [Nat.dvd_one]; exact (Nat.prime_of_mem_primeFactors hp).one_lt.ne'
    rw [hf, prod_inv_distrib]
    have hq := Nat.totient_eq_mul_prod_factors n
    have hr : (n.totient : ℝ) = n * ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
      have := congrArg (fun x : ℚ => (x : ℝ)) hq
      push_cast at this
      exact this
    have htp : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    simp only [one_div]
    rw [eq_div_iff htp.ne', hr]
    have hP : ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hr
      exact htp.ne' hr
    field_simp
    exact div_self (by simpa [one_div] using hP)
  refine Real.tsum_le_of_sum_range_le hnn fun N => ?_
  have hb := hK 1 le_rfl (n : ℤ) (by exact_mod_cast hn0) N
  rw [hprod] at hb
  refine le_trans ?_ hb
  have hsplit : ∑ i ∈ range N, ‖mainWeight i n‖ ≤ ∑ i ∈ Icc 1 N, ‖mainWeight i n‖ := by
    rcases N with _ | N
    · simp
    rw [range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    have h0 : ‖mainWeight 0 n‖ = 0 := by rw [hterm]; simp
    rw [h0, zero_add]
    refine sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => hnn i)
    intro i hi
    rw [mem_Ico] at hi
    rw [mem_Icc]; omega
  refine hsplit.trans (le_of_eq (sum_congr rfl fun q _ => ?_))
  rw [hterm q]
  simp [Int.natAbs_natCast]

/-- P0015 display (6.20), assembled from the two leaves. PROVED from them. -/
theorem mv_620_split : type_of% @Lemma3MV617Integral.mv_620 := by
  obtain ⟨C, hC, hM⟩ := mv_620_main_abs
  refine ⟨C, hC, fun r hr χ hprim hsq hne n hn => ?_⟩
  set K : ℝ := ‖χ ((n : ℤ) : ZMod r)‖ ^ 2 * (r : ℝ) / (r.totient : ℝ) ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hr0 : r ≠ 0 := NeZero.ne r
  have hms := (mv_singular_series_616 n hn).1
  -- the dominating function, supported on the multiples of `r`
  set g : ℕ → ℝ := fun q => if r ∣ q then K * ‖mainWeight (q / r) n‖ else 0 with hg
  have hinj : Function.Injective (fun m : ℕ => r * m) :=
    fun a b h => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hr0) h
  have hsupp : ∀ x ∉ Set.range (fun m : ℕ => r * m), g x = 0 := by
    intro x hx
    have : ¬ r ∣ x := fun ⟨m, hm⟩ => hx ⟨m, hm.symm⟩
    simp [hg, this]
  have hcomp : g ∘ (fun m : ℕ => r * m) = fun m => K * ‖mainWeight m n‖ := by
    funext m
    simp [hg, Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hr0)]
  have hgs : Summable g := by
    rw [← hinj.summable_iff hsupp, hcomp]
    exact hms.mul_left K
  have hgt : ∑' q, g q = K * ∑' m, ‖mainWeight m n‖ := by
    rw [← hinj.tsum_eq (fun x hx => by_contra fun h => hx (hsupp x h))]
    show ∑' m, (g ∘ (fun m : ℕ => r * m)) m = _
    rw [hcomp, tsum_mul_left]
  have hle : ∀ q, ‖crossWeight χ q n‖ ≤ g q := by
    intro q
    by_cases hrq : r ∣ q
    · simp only [hg, hrq, if_true]
      exact mv_620_termwise r hr χ hprim hsq hne n hn q hrq
    · simp only [hg, hrq, if_false]
      rw [crossWeight_of_tau χ n (tauInd_of_not_dvd χ hrq), norm_zero]
  have hcs : Summable (fun q : ℕ => ‖crossWeight χ q n‖) :=
    hgs.of_nonneg_of_le (fun q => norm_nonneg _) hle
  refine ⟨hcs, ?_⟩
  calc ‖∑' q : ℕ, crossWeight χ q n‖ ≤ ∑' q : ℕ, ‖crossWeight χ q n‖ := norm_tsum_le_tsum_norm hcs
    _ ≤ ∑' q, g q := hcs.tsum_le_tsum hle hgs
    _ = K * ∑' m, ‖mainWeight m n‖ := hgt
    _ ≤ K * (C * ((n : ℝ) / (n.totient : ℝ))) := mul_le_mul_of_nonneg_left (hM n hn) hK0
    _ = C * ‖χ ((n : ℤ) : ZMod r)‖ ^ 2 * (r : ℝ) / (r.totient : ℝ) ^ 2 *
          ((n : ℝ) / (n.totient : ℝ)) := by rw [hK]; ring

/-- Exact type twin of the LEAF `Lemma3MV617Integral.mv_620`, PROVED sorry free. -/
theorem mv_620_proved : type_of% @Lemma3MV617Integral.mv_620 := mv_620_split

#print axioms mv_620_termwise
#print axioms mv_620_main_abs
#print axioms mv_620_proved

end LeanLab.ExceptionalSet.UpJ200.Lemma3MV620
