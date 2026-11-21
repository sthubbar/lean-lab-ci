/-
P0069 Baker Harman Pintz 1997, Section 5, page 53 with display 1.8 on page 3 and 5.17 on page 51.
The principal character in 1.8 for the coefficient `(v / D) b1`, used by Prep1121UpslackRoute,
PROVED here with no sorry from the hypotheses on the local density profile `D`: partial
summation against a bounded Lipschitz factor, the comparison `L^A < Y^c1` from Mathlib, b1 vanishes off the integers
with no prime factor below `Y^c1`, so the principal character modulo `q <= L^A` is one on its
support, the termwise identity `(v / D) b1 - v / log Y = (v / D)(b1 - D / log Y)`, and the
assembly. New file, no new definition.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.UpperShortC165Leaves

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b

/-- P0069 page 53 with U-1624: the rescaling `v / D` is bounded by `|v| / c`. PROVED. -/
theorem upslack_lam_bound {v c : ℝ} (hc : 0 < c) {D : ℝ → ℕ → ℝ} (hDc : ∀ x m, c ≤ D x m)
    (x : ℝ) (m : ℕ) : |v / D x m| ≤ |v| / c := by
  have hD : 0 < D x m := lt_of_lt_of_le hc (hDc x m)
  rw [abs_div, abs_of_pos hD]
  exact div_le_div_of_nonneg_left (abs_nonneg v) hc (hDc x m)


/-- A prime factor `p` of `m` other than the prime factor `r` is a prime factor of `m / r`. -/
theorem upslack_mem_primeFactors_div {m p r : ℕ} (hp : p ∈ m.primeFactors)
    (hr : r ∈ m.primeFactors) (hpr : p ≠ r) : p ∈ (m / r).primeFactors := by
  obtain ⟨hpp, hpm, hm0⟩ := Nat.mem_primeFactors.mp hp
  obtain ⟨hrp, hrm, -⟩ := Nat.mem_primeFactors.mp hr
  have hmr : m / r ≠ 0 := by
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hrm
    exact (Nat.div_pos this hrp.pos).ne'
  refine Nat.mem_primeFactors.mpr ⟨hpp, ?_, hmr⟩
  have hm : m = r * (m / r) := (Nat.mul_div_cancel' hrm).symm
  rw [hm] at hpm
  rcases (Nat.Prime.dvd_mul hpp).mp hpm with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hpp hrp).mp h) hpr
  · exact h

/-- The rough indicator vanishes when `n` has a prime factor below `w`. -/
theorem upslack_rough_eq_zero {n p : ℕ} {w : ℝ} (hp : p ∈ n.primeFactors) (hpw : (p : ℝ) < w) :
    upperRough n w = 0 := by
  unfold upperRough
  rw [if_neg]
  intro h
  exact absurd (h p hp) (not_le.mpr hpw)

/-- P0069 page 53: b1 is supported on integers with no prime factor below `Y^c1`. If `m` has a
prime factor `p < Y^c1`, then `p` survives in every cofactor of g, h, j and the kept part of k,
since every prime removed there is at least `Y^c1`, so every rough indicator is zero. PROVED. -/
theorem upslack_raw_eq_zero_of_small_prime {ε Y : ℝ} {m p : ℕ} (hp : p ∈ m.primeFactors)
    (hpY : (p : ℝ) < Y ^ upperC1 ε) : upperRawWeight ε Y m = 0 := by
  have hne : ∀ r : ℕ, Y ^ upperC1 ε ≤ (r : ℝ) → p ≠ r := by
    intro r hr h; subst h; linarith
  have hg : upperG ε Y m = 0 := upslack_rough_eq_zero hp hpY
  have hh : upperH ε Y m = 0 := by
    unfold upperH
    refine Finset.sum_eq_zero fun p1 hp1 => ?_
    obtain ⟨hp1m, hp1Y, -⟩ := Finset.mem_filter.mp hp1
    exact upslack_rough_eq_zero (upslack_mem_primeFactors_div hp hp1m (hne p1 hp1Y)) hpY
  have hj : upperJ ε Y m = 0 := by
    unfold upperJ
    refine Finset.sum_eq_zero fun p1 hp1 => Finset.sum_eq_zero fun p2 hp2 => ?_
    obtain ⟨hp1m, hp1Y, -⟩ := Finset.mem_filter.mp hp1
    obtain ⟨hp2m, hp2Y, -⟩ := Finset.mem_filter.mp hp2
    have h1 := upslack_mem_primeFactors_div hp hp1m (hne p1 hp1Y)
    exact upslack_rough_eq_zero (upslack_mem_primeFactors_div h1 hp2m (hne p2 hp2Y)) hpY
  have hk : upperKept ε Y m = 0 := by
    unfold upperKept
    refine Finset.sum_eq_zero fun p1 hp1 => Finset.sum_eq_zero fun p2 hp2 =>
      Finset.sum_eq_zero fun p3 hp3 => ?_
    obtain ⟨hp1m, hp1Y, -⟩ := Finset.mem_filter.mp hp1
    obtain ⟨hp2m, hp2Y, -⟩ := Finset.mem_filter.mp hp2
    obtain ⟨hp3m, hp3Y, -⟩ := Finset.mem_filter.mp hp3
    have h1 := upslack_mem_primeFactors_div hp hp1m (hne p1 hp1Y)
    have h2 := upslack_mem_primeFactors_div h1 hp2m (hne p2 hp2Y)
    have h3 := upslack_mem_primeFactors_div h2 hp3m (hne p3 hp3Y)
    split_ifs
    · exact upslack_rough_eq_zero h3 (lt_of_lt_of_le hpY hp3Y)
    · rfl
  unfold upperRawWeight
  rw [hg, hh, hj, hk]; ring

/-- P0069 page 3 with page 53, PROVED: a power of `log x` is eventually below `Y^c1`, where
`Y = x^(11/20+eps)` and `c1 = (1 + 7 theta2)/15 - eps >= 1/9`. A Mathlib lookup on
`log x ^ A = o(x ^ b)` for `b > 0`. -/
theorem upslack_log_pow_lt_rough_level {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (A : ℝ) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → Real.log x ^ A < (x ^ (11 / 20 + ε)) ^ upperC1 ε := by
  have hc1 := upperC1_ge hε8
  have hb : 0 < (11 / 20 + ε) * upperC1 ε := mul_pos (by linarith) (by linarith)
  have h := (isLittleO_log_rpow_rpow_atTop A hb).bound (by norm_num : (0 : ℝ) < 1 / 2)
  rw [Filter.eventually_atTop] at h
  obtain ⟨X, hX⟩ := h
  refine ⟨max X 2, fun x hx => ?_⟩
  have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
  have h1 := hX x (le_trans (le_max_left _ _) hx)
  rw [← Real.rpow_mul (by linarith)]
  have hpos : 0 < x ^ ((11 / 20 + ε) * upperC1 ε) := Real.rpow_pos_of_pos (by linarith) _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpos] at h1
  calc Real.log x ^ A ≤ |Real.log x ^ A| := le_abs_self _
    _ ≤ 1 / 2 * x ^ ((11 / 20 + ε) * upperC1 ε) := h1
    _ < x ^ ((11 / 20 + ε) * upperC1 ε) := by linarith

/-- Abel partial summation against a bounded Lipschitz factor, PROVED, for the step "partial
summation" behind 1.8 on page 3 from 5.17 on page 51. If every prefix sum of `a` over `s` up to
`t <= T` is at most `B` in absolute value, `|f| <= F` on `s`, and `f` is `G`-Lipschitz on `s`,
which lies in `(u, w]`, then every prefix sum of `f a` is at most `(F + G (w - u)) B`. Write the
sum as `f(m_k) S_k` minus the sum of `(f(m_(i+1)) - f(m_i)) S_i`, by induction from the top. -/
theorem upslack_abel_lipschitz {s : Finset ℕ} {u w : ℕ} (huw : u ≤ w)
    (hs : s ⊆ Finset.Ioc u w) (a f : ℕ → ℝ) {F G B T : ℝ} (hF0 : 0 ≤ F) (hG : 0 ≤ G)
    (hF : ∀ m ∈ s, |f m| ≤ F)
    (hfG : ∀ m ∈ s, ∀ m' ∈ s, |f m - f m'| ≤ G * |(m : ℝ) - m'|)
    (hB : ∀ t : ℝ, t ≤ T → |∑ m ∈ s.filter (fun m : ℕ => (m : ℝ) ≤ t), a m| ≤ B)
    (t : ℝ) (ht : t ≤ T) :
    |∑ m ∈ s.filter (fun m : ℕ => (m : ℝ) ≤ t), f m * a m| ≤ (F + G * ((w : ℝ) - u)) * B := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB T le_rfl)
  have hsu : ∀ m ∈ s, u < m ∧ m ≤ w := fun m hm => Finset.mem_Ioc.mp (hs hm)
  -- the key claim, by induction on the prefix from its largest element
  have key : ∀ S : Finset ℕ, S ⊆ s → (∀ m ∈ S, (m : ℝ) ≤ T) →
      (∀ m ∈ s, ∀ m' ∈ S, m ≤ m' → m ∈ S) →
      ∀ M ∈ S, (∀ m ∈ S, m ≤ M) →
      |∑ m ∈ S, f m * a m - f M * ∑ m ∈ S, a m| ≤ G * ((M : ℝ) - u) * B := by
    intro S
    induction S using Finset.induction_on_max with
    | empty => intro _ _ _ M hM; simp at hM
    | insert b S0 hlt ih =>
      intro hsub hT hdc M hM hmax
      have hbS : b ∈ insert b S0 := Finset.mem_insert_self _ _
      have hb0 : b ∉ S0 := fun h => lt_irrefl _ (hlt b h)
      have hMb : M = b := by
        rcases Finset.mem_insert.mp hM with h | h
        · exact h
        · exact absurd (hmax b hbS) (not_le.mpr (hlt M h))
      subst hMb
      have hbs : M ∈ s := hsub hbS
      have hub : (u : ℝ) < M := by exact_mod_cast (hsu M hbs).1
      rw [Finset.sum_insert hb0, Finset.sum_insert hb0]
      rcases S0.eq_empty_or_nonempty with h0 | hne
      · subst h0
        simp only [Finset.sum_empty, add_zero, sub_self, abs_zero]
        exact mul_nonneg (mul_nonneg hG (by linarith)) hB0
      · set M0 := S0.max' hne
        have hM0 : M0 ∈ S0 := Finset.max'_mem _ _
        have hM0max : ∀ m ∈ S0, m ≤ M0 := fun m hm => Finset.le_max' _ _ hm
        have hM0lt : M0 < M := hlt M0 hM0
        have hsub0 : S0 ⊆ s := fun m hm => hsub (Finset.mem_insert_of_mem hm)
        have hT0 : ∀ m ∈ S0, (m : ℝ) ≤ T := fun m hm => hT m (Finset.mem_insert_of_mem hm)
        have hdc0 : ∀ m ∈ s, ∀ m' ∈ S0, m ≤ m' → m ∈ S0 := by
          intro m hm m' hm' hle
          rcases Finset.mem_insert.mp (hdc m hm m' (Finset.mem_insert_of_mem hm') hle) with h | h
          · exact absurd (h ▸ hle) (not_le.mpr (hlt m' hm'))
          · exact h
        have ih' := ih hsub0 hT0 hdc0 M0 hM0 hM0max
        have hfilt : s.filter (fun m : ℕ => (m : ℝ) ≤ (M0 : ℝ)) = S0 := by
          ext m
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hm, hle⟩
            exact hdc0 m hm M0 hM0 (by exact_mod_cast hle)
          · intro hm
            exact ⟨hsub0 hm, by exact_mod_cast hM0max m hm⟩
        have hA : |∑ m ∈ S0, a m| ≤ B := by
          have := hB (M0 : ℝ) (hT0 M0 hM0)
          rwa [hfilt] at this
        have hf : |f M0 - f M| ≤ G * ((M : ℝ) - M0) := by
          have := hfG M0 (hsub0 hM0) M hbs
          have hd : |((M0 : ℕ) : ℝ) - (M : ℝ)| = (M : ℝ) - M0 := by
            rw [abs_sub_comm, abs_of_nonneg]
            have : (M0 : ℝ) < M := by exact_mod_cast hM0lt
            linarith
          rwa [hd] at this
        have e : f M * a M + ∑ m ∈ S0, f m * a m - f M * (a M + ∑ m ∈ S0, a m) =
            (∑ m ∈ S0, f m * a m - f M0 * ∑ m ∈ S0, a m) +
              (f M0 - f M) * ∑ m ∈ S0, a m := by ring
        rw [e]
        calc _ ≤ |∑ m ∈ S0, f m * a m - f M0 * ∑ m ∈ S0, a m| +
              |(f M0 - f M) * ∑ m ∈ S0, a m| := abs_add_le _ _
          _ ≤ G * ((M0 : ℝ) - u) * B + G * ((M : ℝ) - M0) * B := by
              rw [abs_mul]
              have := mul_le_mul hf hA (abs_nonneg _) (mul_nonneg hG (by
                have : (M0 : ℝ) < M := by exact_mod_cast hM0lt
                linarith))
              linarith
          _ = G * ((M : ℝ) - u) * B := by ring
  set S := s.filter (fun m : ℕ => (m : ℝ) ≤ t) with hS
  have hwu : (u : ℝ) ≤ w := by exact_mod_cast huw
  rcases S.eq_empty_or_nonempty with h0 | hne
  · rw [h0, Finset.sum_empty, abs_zero]
    exact mul_nonneg (add_nonneg hF0 (mul_nonneg hG (by linarith))) hB0
  · set M := S.max' hne
    have hM : M ∈ S := Finset.max'_mem _ _
    have hMs : M ∈ s := (Finset.mem_filter.mp hM).1
    have hk := key S (Finset.filter_subset _ _)
      (fun m hm => le_trans (Finset.mem_filter.mp hm).2 ht)
      (fun m hm m' hm' hle => Finset.mem_filter.mpr
        ⟨hm, le_trans (by exact_mod_cast hle) (Finset.mem_filter.mp hm').2⟩)
      M hM (fun m hm => Finset.le_max' _ _ hm)
    have hA : |∑ m ∈ S, a m| ≤ B := hB t ht
    have hfM : |f M| ≤ F := hF M hMs
    have hMw : (M : ℝ) - u ≤ (w : ℝ) - u := by
      have : (M : ℝ) ≤ w := by exact_mod_cast (hsu M hMs).2
      linarith
    have e : ∑ m ∈ S, f m * a m =
        (∑ m ∈ S, f m * a m - f M * ∑ m ∈ S, a m) + f M * ∑ m ∈ S, a m := by ring
    rw [e]
    calc _ ≤ |∑ m ∈ S, f m * a m - f M * ∑ m ∈ S, a m| + |f M * ∑ m ∈ S, a m| :=
          abs_add_le _ _
      _ ≤ G * ((M : ℝ) - u) * B + F * B := by
          rw [abs_mul]
          have := mul_le_mul hfM hA (abs_nonneg _) hF0
          linarith
      _ ≤ G * ((w : ℝ) - u) * B + F * B := by
          have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMw hG) hB0
          linarith
      _ = (F + G * ((w : ℝ) - u)) * B := by ring

/-- P0069 page 53: the Lipschitz bound for `v / D` on J from that of `D` and `D >= c > 0`. PROVED. -/
theorem upslack_inv_lipschitz {ε x v c K : ℝ} (hc : 0 < c) {D : ℝ → ℕ → ℝ}
    (hDc : ∀ x m, c ≤ D x m) (hY : 0 < x ^ (11 / 20 + ε))
    (hDLip : ∀ m ∈ rightInterval ε x, ∀ m' ∈ rightInterval ε x,
      |D x m - D x m'| ≤ K * |(m : ℝ) - m'| / x ^ (11 / 20 + ε))
    {m m' : ℕ} (hm : m ∈ rightInterval ε x) (hm' : m' ∈ rightInterval ε x) :
    |v / D x m - v / D x m'| ≤
      |v| * |K| / (c ^ 2 * x ^ (11 / 20 + ε)) * |(m : ℝ) - m'| := by
  set Y := x ^ (11 / 20 + ε)
  have h1 := hDc x m
  have h2 := hDc x m'
  have hp1 : 0 < D x m := lt_of_lt_of_le hc h1
  have hp2 : 0 < D x m' := lt_of_lt_of_le hc h2
  have hprod : 0 < D x m * D x m' := mul_pos hp1 hp2
  have hc2 : c ^ 2 ≤ D x m * D x m' := by nlinarith
  have e : v / D x m - v / D x m' = v * (D x m' - D x m) / (D x m * D x m') := by
    field_simp
  have hL : |D x m' - D x m| ≤ |K| * |(m : ℝ) - m'| / Y := by
    have := hDLip m' hm' m hm
    rw [abs_sub_comm ((m' : ℝ)) m] at this
    refine le_trans this ?_
    apply div_le_div_of_nonneg_right _ hY.le
    exact mul_le_mul_of_nonneg_right (le_abs_self K) (abs_nonneg _)
  set Z := |v| * (|K| * |(m : ℝ) - m'| / Y) with hZ
  have hZ0 : 0 ≤ Z := by positivity
  rw [e, abs_div, abs_mul, abs_of_pos hprod]
  calc |v| * |D x m' - D x m| / (D x m * D x m') ≤ Z / (D x m * D x m') := by
        apply div_le_div_of_nonneg_right _ hprod.le
        exact mul_le_mul_of_nonneg_left hL (abs_nonneg v)
    _ ≤ Z / c ^ 2 := div_le_div_of_nonneg_left hZ0 (by positivity) hc2
    _ = |v| * |K| / (c ^ 2 * Y) * |(m : ℝ) - m'| := by
        rw [hZ]; field_simp

/-- P0069 page 53 with page 3: on J, for `Y >= 2` and the principal character modulo
`q < Y^c1`, the summand of 1.8 for `(v / D) b1` is `(v / D)(b1 - D / log Y)`. PROVED. -/
theorem upslack_principal_term {ε x v c : ℝ} (hc : 0 < c) {D : ℝ → ℕ → ℝ}
    (hDc : ∀ x m, c ≤ D x m) (hY2 : 2 ≤ x ^ (11 / 20 + ε)) {q : ℕ}
    (hq : 1 ≤ q) (hqY : (q : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε)
    {m : ℕ} (hm : m ∈ rightInterval ε x) :
    (upperNormCoeff ε (fun x m => v / D x m) x m : ℂ) *
        (1 : DirichletCharacter ℂ q) (m : ZMod q) -
      Thm2.delta (1 : DirichletCharacter ℂ q) * (v : ℂ) / Real.log (x ^ (11 / 20 + ε)) =
      (((v / D x m) * (upperRawWeight ε (x ^ (11 / 20 + ε)) m -
        D x m / Real.log (x ^ (11 / 20 + ε))) : ℝ) : ℂ) := by
  have hD : D x m ≠ 0 := (lt_of_lt_of_le hc (hDc x m)).ne'
  have hδ : Thm2.delta (1 : DirichletCharacter ℂ q) = 1 := by simp [Thm2.delta]
  have hDc' : ((D x m : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hD
  have hL : Real.log (x ^ (11 / 20 + ε)) ≠ 0 := (Real.log_pos (by linarith)).ne'
  have hLc : ((Real.log (x ^ (11 / 20 + ε)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hL
  unfold upperNormCoeff
  rw [if_pos ⟨hY2, hm⟩, hδ]
  by_cases hr : upperRawWeight ε (x ^ (11 / 20 + ε)) m = 0
  · rw [hr]; push_cast; field_simp; ring
  · have hcop : m.Coprime q := by
      apply Nat.coprime_of_dvd
      intro k hk hkm hkq
      have hm0 : m ≠ 0 := by
        have := (Finset.mem_Ioc.mp hm).1; omega
      have hkmem : k ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hk, hkm, hm0⟩
      by_cases hlt : (k : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε
      · exact hr (upslack_raw_eq_zero_of_small_prime hkmem hlt)
      · have hkq' : (k : ℝ) ≤ q := by exact_mod_cast Nat.le_of_dvd (by omega) hkq
        linarith [not_lt.mp hlt]
    have hχ : (1 : DirichletCharacter ℂ q) (m : ZMod q) = 1 :=
      MulChar.one_apply ((ZMod.isUnit_iff_coprime m q).mpr hcop)
    rw [hχ]; push_cast; field_simp

/-- Page 3 display 1.8, principal character, for `(v / D) b1`, PROVED: rewrite each summand as `(v / D)(b1 - D / log Y)` using the support of b1, then apply the
partial summation leaf with `F = |v| / c`, `G = |v| |K| / (c^2 Y)` and the prefix bound of the
density leaf, the interval J having length at most `2 Y`. -/
theorem upslack_principal_prefix_split
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (v : ℝ) {D : ℝ → ℕ → ℝ} {c K : ℝ}
    (hc : 0 < c) (hDc : ∀ x m, c ≤ D x m)
    (hDLip : ∀ x : ℝ, ∀ m ∈ rightInterval ε x, ∀ m' ∈ rightInterval ε x,
      |D x m - D x m'| ≤ K * |(m : ℝ) - m'| / x ^ (11 / 20 + ε))
    (hDpre : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
      |∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
        (upperRawWeight ε (x ^ (11 / 20 + ε)) m - D x m / Real.log (x ^ (11 / 20 + ε)))| ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A))
    {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
      ∀ χ : DirichletCharacter ℂ q, χ = 1 → ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
        ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((upperNormCoeff ε (fun x m => v / D x m) x m : ℂ) * χ (m : ZMod q) -
            Thm2.delta χ * (v : ℂ) / Real.log (x ^ (11 / 20 + ε)))‖ ≤
            C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  obtain ⟨Cp, hp⟩ := hDpre A hA
  obtain ⟨X1, hX1⟩ := upslack_log_pow_lt_rough_level hε hε8 A
  set M := |v| / c + 2 * |v| * |K| / c ^ 2 with hM
  refine ⟨max (max (max Cp X1) 4) (M * Cp), ?_⟩
  intro x hx q hq hqx χ hχ t ht
  subst hχ
  have hx4 : 4 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxp : Cp ≤ x :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have hxX : X1 ≤ x :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have hxM : M * Cp ≤ x := le_trans (le_max_right _ _) hx
  have hY2 := upper_Y_ge_two hε hx4
  set Y := x ^ (11 / 20 + ε) with hYdef
  have hY0 : 0 < Y := by linarith
  have hqY : (q : ℝ) < Y ^ upperC1 ε := lt_of_le_of_lt hqx (hX1 x hxX)
  rw [Finset.sum_congr rfl fun m hm =>
    upslack_principal_term hc hDc hY2 hq hqY (Finset.mem_filter.mp hm).1]
  rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
  have hB : ∀ t' : ℝ, t' ≤ 2 * Y →
      |∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t'),
        (upperRawWeight ε Y m - D x m / Real.log Y)| ≤ Cp * Y * Real.log x ^ (-A) :=
    hp x hxp
  have hB0 : 0 ≤ Cp * Y * Real.log x ^ (-A) := le_trans (abs_nonneg _) (hB (2 * Y) le_rfl)
  have hG0 : 0 ≤ |v| * |K| / (c ^ 2 * Y) := by positivity
  have habel := upslack_abel_lipschitz (s := rightInterval ε x)
    (u := ⌊Y⌋₊) (w := ⌊2 * Y⌋₊) (Nat.floor_mono (by linarith))
    (by unfold rightInterval; exact Finset.Subset.refl _)
    (fun m => upperRawWeight ε Y m - D x m / Real.log Y) (fun m => v / D x m)
    (F := |v| / c) (G := |v| * |K| / (c ^ 2 * Y)) (B := Cp * Y * Real.log x ^ (-A))
    (T := 2 * Y) (by positivity) hG0
    (fun m _ => upslack_lam_bound hc hDc x m)
    (fun m hm m' hm' => upslack_inv_lipschitz hc hDc hY0 (hDLip x) hm hm') hB t ht
  have hlen : ((⌊2 * Y⌋₊ : ℕ) : ℝ) - (⌊Y⌋₊ : ℕ) ≤ 2 * Y := by
    have h1 : ((⌊2 * Y⌋₊ : ℕ) : ℝ) ≤ 2 * Y := Nat.floor_le (by linarith)
    have h2 : Y - 1 < ((⌊Y⌋₊ : ℕ) : ℝ) := Nat.sub_one_lt_floor Y
    linarith
  have hGlen : |v| * |K| / (c ^ 2 * Y) * (((⌊2 * Y⌋₊ : ℕ) : ℝ) - (⌊Y⌋₊ : ℕ)) ≤
      2 * |v| * |K| / c ^ 2 := by
    calc |v| * |K| / (c ^ 2 * Y) * (((⌊2 * Y⌋₊ : ℕ) : ℝ) - (⌊Y⌋₊ : ℕ))
        ≤ |v| * |K| / (c ^ 2 * Y) * (2 * Y) := mul_le_mul_of_nonneg_left hlen hG0
      _ = 2 * |v| * |K| / c ^ 2 := by field_simp
  have hR0 : 0 ≤ Y * Real.log x ^ (-A) :=
    mul_nonneg hY0.le (Real.rpow_nonneg (Real.log_nonneg (by linarith)) _)
  calc _ ≤ (|v| / c + |v| * |K| / (c ^ 2 * Y) * (((⌊2 * Y⌋₊ : ℕ) : ℝ) - (⌊Y⌋₊ : ℕ))) *
          (Cp * Y * Real.log x ^ (-A)) := habel
    _ ≤ M * (Cp * Y * Real.log x ^ (-A)) := by
        apply mul_le_mul_of_nonneg_right _ hB0
        rw [hM]; linarith
    _ = (M * Cp) * (Y * Real.log x ^ (-A)) := by ring
    _ ≤ max (max (max Cp X1) 4) (M * Cp) * (Y * Real.log x ^ (-A)) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hR0
    _ = _ := by ring

end LeanLab.BHP1997.DecompC165d
