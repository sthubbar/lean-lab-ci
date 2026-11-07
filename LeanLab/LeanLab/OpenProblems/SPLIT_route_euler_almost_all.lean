import LeanLab.OpenProblems.State1612

/-!
# Split of `route_euler_almost_all` (OpenProblems, State1612)

The target says the exception count `euExc X` is `o(X)`. This file reduces it to four strictly
easier leaves and assembles the target from them without any of the four.

The route, written out.  Write `m_n = 8n + 3`.  A representation `m = x ^ 2 + 2 * p` has `x` odd,
and the list form `4n + 1 = p + 2k(k+1)` of the source file is a bijection, so a multiplicity
`R n`, the number of `k` with `4n + 1 - 2k(k+1)` prime, vanishes exactly at the exceptions.

1. `leaf_representation_multiplicity`: such an `R`, given by a finite list search, exists.
2. `leaf_circle_method_variance`: the mean value of `R` on a scale is a main term `m` of size at
   least a fixed multiple of `sqrt n / log n`, and the second moment of `R - m` over `[1, X]` is
   at most a constant times `X ^ 2 / (log X) ^ 3`.  The shrinking of the second moment leaves a
   `log X` to spare against the square of the main term.
3. `leaf_exception_count_dyadic`: the level-set estimate.  An `n` counted by `euExc` has `R` at `0`
   and the main term at least `c / log X`, so the second moment controls the count, and at the
   scales `X = 2 ^ k` the count is below `epsilon * X` for every positive `epsilon`.
4. `leaf_dyadic_to_all_X`: `euExc` is monotone and each `X` sits in `[2 ^ k, 2 ^ (k+1))`, so the
   estimate at the powers of two carries to every `X` with `epsilon` halved.
-/

namespace LeanLab.OpenProblems.State1612

open LeanLab

/-- LEAF 1, multiplicity.  There is a multiplicity `R n`, computed from the list form as the
number of `k` with `4n + 1 - 2k(k+1)` prime, and for `1 ≤ n` it vanishes exactly where `8n + 3`
has no odd square plus twice a prime.  The bound `4n + 2` on `k` is safe: a term with
`2k(k+1) > 4n + 1` truncates to `0`, which is not prime, and every true solution has `k ≤ n`. -/
theorem leaf_representation_multiplicity :
    ∃ R : ℕ → ℕ,
      (∀ n : ℕ, R n = ((Finset.range (4 * n + 2)).filter
          (fun k => (4 * n + 1 - 2 * k * (k + 1)).Prime)).card) ∧
      ∀ n : ℕ, 1 ≤ n → (R n ≠ 0 ↔ IsEuler (8 * n + 3)) := by
  classical
  refine ⟨fun n => ((Finset.range (4 * n + 2)).filter
      (fun k => (4 * n + 1 - 2 * k * (k + 1)).Prime)).card, fun n => rfl, ?_⟩
  intro n hn
  rw [isEuler_iff_triangular]
  constructor
  · intro hne
    have hne' : ((Finset.range (4 * n + 2)).filter
        (fun k => (4 * n + 1 - 2 * k * (k + 1)).Prime)).card ≠ 0 := hne
    rw [Finset.card_ne_zero] at hne'
    obtain ⟨k, hk⟩ := hne'
    rw [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨-, hp⟩ := hk
    have hpk : 4 * n + 1 - 2 * k * (k + 1) ≠ 0 := hp.ne_zero
    exact ⟨k, _, hp, by omega⟩
  · rintro ⟨k, p, hp, he⟩
    have hp2 : 2 ≤ p := hp.two_le
    have hX : 2 * k * (k + 1) ≤ 4 * n + 1 := by omega
    have hk2 : 2 * k ≤ 2 * k * (k + 1) := by nlinarith
    have hk : k < 4 * n + 2 := by omega
    have hsub : 4 * n + 1 - 2 * k * (k + 1) = p := by omega
    show ((Finset.range (4 * n + 2)).filter
        (fun k => (4 * n + 1 - 2 * k * (k + 1)).Prime)).card ≠ 0
    rw [Finset.card_ne_zero]
    exact ⟨k, by rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hk, by rw [hsub]; exact hp⟩⟩

/-- LEAF 2, mean value and second moment.  For the multiplicity `R` of LEAF 1 there are a main
term `m`, positive constants `B` and `c`, with `m n` at least `c * sqrt n / log n` on `1 ≤ n` and
the second moment of `R - m` over `[1, X]` at most `B * X ^ 2 / (log X) ^ 3`.  This is the only
analytic input of the route: the sum over the circle is dominated except near rationals with small
denominator, the singular series is bounded below so the main term keeps a fixed fraction of
`sqrt n / log n`, and the mean square of the error gains a whole power of the logarithm. -/
theorem leaf_circle_method_variance (R : ℕ → ℕ)
    (hR : ∀ n : ℕ, 1 ≤ n → (R n ≠ 0 ↔ IsEuler (8 * n + 3))) :
    ∃ (m : ℕ → ℝ) (B c : ℝ), 0 < B ∧ 0 < c ∧
      (∀ n : ℕ, 1 ≤ n → c * Real.sqrt (n : ℝ) / Real.log (n : ℝ) ≤ m n) ∧
      ∀ᶠ X : ℕ in Filter.atTop,
        Finset.sum (Finset.Icc 1 X) (fun n => ((R n : ℝ) - m n) ^ 2) ≤
          B * (X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 3 := by
  sorry

private theorem card_pred_mul_le_two_sum (s : Finset ℕ) :
    (s.card : ℝ) * ((s.card : ℝ) - 1) ≤ 2 * s.sum (fun n => (n : ℝ)) := by
  classical
  suffices H : ∀ n : ℕ, ∀ s : Finset ℕ, s.card = n →
      (s.card : ℝ) * ((s.card : ℝ) - 1) ≤ 2 * s.sum (fun n => (n : ℝ)) from H s.card s rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs
    rcases s.eq_empty_or_nonempty with h | hne
    · subst h
      simp
    · have hmem : s.max' hne ∈ s := Finset.max'_mem s hne
      have hcard : (s.erase (s.max' hne)).card = n - 1 := by
        rw [Finset.card_erase_of_mem hmem, hs]
      have hn1 : 1 ≤ n := by rw [← hs]; exact Finset.card_pos.mpr hne
      have ihn := ih (n - 1) (by omega) (s.erase (s.max' hne)) hcard
      have hmax : ((n : ℝ) - 1) ≤ ((s.max' hne : ℕ) : ℝ) := by
        have hsub : s ⊆ Finset.range (s.max' hne + 1) := by
          intro x hx
          simp only [Finset.mem_range]
          have hx' : x ≤ s.max' hne := Finset.le_max' s x hx
          omega
        have h1 : s.card ≤ s.max' hne + 1 := by
          calc s.card ≤ (Finset.range (s.max' hne + 1)).card := Finset.card_le_card hsub
            _ = s.max' hne + 1 := Finset.card_range _
        have h2 : n ≤ s.max' hne + 1 := by omega
        have h3 : (n : ℝ) ≤ ((s.max' hne : ℕ) : ℝ) + 1 := by exact_mod_cast h2
        linarith
      have hsum : s.sum (fun n => (n : ℝ))
          = ((s.max' hne : ℕ) : ℝ) + (s.erase (s.max' hne)).sum (fun n => (n : ℝ)) := by
        rw [← Finset.sum_erase_add s (fun n => (n : ℝ)) hmem]
        ring
      have hcast : ((s.erase (s.max' hne)).card : ℝ) = (n : ℝ) - 1 := by
        rw [hcard, Nat.cast_sub hn1]
        norm_num
      rw [hcast] at ihn
      rw [hs, hsum]
      nlinarith

/-- LEAF 3, level set at the powers of two.  With the multiplicity of LEAF 1 and the main term and
second moment of LEAF 2, every positive `epsilon` has the exceptions below `epsilon * 2 ^ k` for
all large `k`.  A counted `n ≤ X = 2 ^ k` satisfies `R n = 0`, so `(R n - m n) ^ 2 = (m n) ^ 2` and
`m n` is at least `c / log X`; the second moment then bounds the count by `(B / c ^ 2) * X / log X`,
and `log X` grows without bound while `B / c ^ 2` stays fixed. -/
theorem leaf_exception_count_dyadic (R : ℕ → ℕ) (m : ℕ → ℝ) (B c : ℝ)
    (hB : 0 < B) (hc : 0 < c)
    (hR : ∀ n : ℕ, 1 ≤ n → (R n ≠ 0 ↔ IsEuler (8 * n + 3)))
    (hmain : ∀ n : ℕ, 1 ≤ n → c * Real.sqrt (n : ℝ) / Real.log (n : ℝ) ≤ m n)
    (hvar : ∀ᶠ X : ℕ in Filter.atTop,
      Finset.sum (Finset.Icc 1 X) (fun n => ((R n : ℝ) - m n) ^ 2) ≤
        B * (X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 3) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in Filter.atTop, (euExc (2 ^ k) : ℝ) ≤ ε * ((2 ^ k : ℕ) : ℝ) := by
  intro ε hε
  classical
  set C : ℝ := B / c ^ 2 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  obtain ⟨X0, hX0⟩ := Filter.eventually_atTop.mp hvar
  obtain ⟨K1, hK1⟩ := exists_nat_ge (16 * C / ε ^ 2 / 0.6931471803)
  obtain ⟨K2, hK2⟩ := exists_nat_ge (8 / ε)
  rw [Filter.eventually_atTop]
  refine ⟨max (max X0 K1) (max K2 2), fun k hk => ?_⟩
  have hkX0 : X0 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk
  have hkK1 : K1 ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk
  have hkK2 : K2 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hk2 : 2 ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  set X : ℕ := 2 ^ k with hXdef
  have hX2 : 2 ≤ X := by rw [hXdef]; exact le_of_lt (lt_of_le_of_lt hk2 k.lt_two_pow_self)
  have hX1 : 1 < X := by omega
  have hkX : k ≤ X := by rw [hXdef]; exact le_of_lt k.lt_two_pow_self
  have hxpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast hX1)
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlogbig : 16 * C / ε ^ 2 ≤ Real.log (X : ℝ) := by
    rw [hXdef]
    have hXeq : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
    rw [hXeq, Real.log_pow]
    have hk1 : (16 * C / ε ^ 2 / 0.6931471803 : ℝ) ≤ (k : ℝ) :=
      le_trans hK1 (by exact_mod_cast hkK1)
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
    have hstep1 : 16 * C / ε ^ 2 / 0.6931471803 * 0.6931471803 ≤ (k : ℝ) * 0.6931471803 :=
      mul_le_mul_of_nonneg_right hk1 (by norm_num)
    have hstep2 : 16 * C / ε ^ 2 / 0.6931471803 * 0.6931471803 = 16 * C / ε ^ 2 := by
      field_simp
    rw [hstep2] at hstep1
    have hstep3 : (k : ℝ) * 0.6931471803 ≤ (k : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left hlog2.le hk0
    linarith
  have hεX : 8 ≤ ε * (X : ℝ) := by
    have hk2' : (8 / ε : ℝ) ≤ (k : ℝ) := le_trans hK2 (by exact_mod_cast hkK2)
    have h1 : (8 / ε : ℝ) ≤ (X : ℝ) := le_trans hk2' (by exact_mod_cast hkX)
    have := mul_le_mul_of_nonneg_left h1 (le_of_lt hε)
    rwa [mul_div_cancel₀ (8 : ℝ) (ne_of_gt hε)] at this
  -- the index set, `n = 1` is never an exception
  set T : Finset ℕ := (Finset.Icc 2 X).filter (fun n => ¬ IsEuler (8 * n + 3)) with hTe
  have heuExc : euExc X = T.card := by
    rw [hTe]
    unfold euExc
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, hni⟩
      have hn2 : 2 ≤ n := by
        rcases Nat.lt_or_ge 1 n with h | h
        · omega
        · have hn1 : n = 1 := by omega
          subst hn1
          exact absurd isEuler_eleven hni
      exact ⟨⟨hn2, h2⟩, hni⟩
    · rintro ⟨⟨h2, h3⟩, hni⟩
      exact ⟨⟨by omega, h3⟩, hni⟩
  -- pointwise bound on `T`
  have hpt : ∀ n ∈ T, c ^ 2 / (Real.log (X : ℝ)) ^ 2 * (n : ℝ) ≤ ((R n : ℝ) - m n) ^ 2 := by
    intro n hn
    rw [hTe, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn2, hnX⟩, hni⟩ := hn
    have hn1 : 1 ≤ n := by omega
    have hRn : R n = 0 := by
      by_contra h
      exact hni ((hR n hn1).mp h)
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hlogle : Real.log (n : ℝ) ≤ Real.log (X : ℝ) :=
      (Real.log_le_log_iff (by linarith) hxpos).mpr (by exact_mod_cast hnX)
    have hmn : c * Real.sqrt (n : ℝ) / Real.log (n : ℝ) ≤ m n := hmain n hn1
    have hbase : 0 ≤ c * Real.sqrt (n : ℝ) / Real.log (n : ℝ) := by positivity
    have hsq : (c * Real.sqrt (n : ℝ) / Real.log (n : ℝ)) ^ 2 ≤ (m n) ^ 2 :=
      pow_le_pow_left₀ hbase hmn 2
    have hsqrt : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt (le_of_lt hnpos)
    have hval : (c * Real.sqrt (n : ℝ) / Real.log (n : ℝ)) ^ 2
        = c ^ 2 * (n : ℝ) / (Real.log (n : ℝ)) ^ 2 := by
      rw [div_pow, mul_pow, hsqrt]
    have hfrac : c ^ 2 / (Real.log (X : ℝ)) ^ 2 ≤ c ^ 2 / (Real.log (n : ℝ)) ^ 2 := by
      refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
      nlinarith
    have hsub : ((R n : ℝ) - m n) ^ 2 = (m n) ^ 2 := by
      rw [hRn]
      push_cast
      ring
    calc c ^ 2 / (Real.log (X : ℝ)) ^ 2 * (n : ℝ)
        ≤ c ^ 2 / (Real.log (n : ℝ)) ^ 2 * (n : ℝ) :=
          mul_le_mul_of_nonneg_right hfrac (le_of_lt hnpos)
      _ = (c * Real.sqrt (n : ℝ) / Real.log (n : ℝ)) ^ 2 := by rw [hval]; ring
      _ ≤ (m n) ^ 2 := hsq
      _ = ((R n : ℝ) - m n) ^ 2 := by rw [hsub]
  have hsumT : c ^ 2 / (Real.log (X : ℝ)) ^ 2 * T.sum (fun n => (n : ℝ))
      ≤ T.sum (fun n => ((R n : ℝ) - m n) ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hpt
  have hsub2 : T.sum (fun n => ((R n : ℝ) - m n) ^ 2)
      ≤ Finset.sum (Finset.Icc 1 X) (fun n => ((R n : ℝ) - m n) ^ 2) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro n hn
      rw [hTe, Finset.mem_filter, Finset.mem_Icc] at hn
      simp only [Finset.mem_Icc]
      omega
    · intro n _ _
      positivity
  have hvarX : Finset.sum (Finset.Icc 1 X) (fun n => ((R n : ℝ) - m n) ^ 2)
      ≤ B * (X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 3 := hX0 X (le_trans hkX0 hkX)
  have hbound : T.sum (fun n => (n : ℝ)) ≤ C * (X : ℝ) ^ 2 / Real.log (X : ℝ) := by
    have hq : c ^ 2 / (Real.log (X : ℝ)) ^ 2 * T.sum (fun n => (n : ℝ))
        ≤ B * (X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 3 := le_trans hsumT (le_trans hsub2 hvarX)
    have hc2pos : 0 < c ^ 2 / (Real.log (X : ℝ)) ^ 2 := by positivity
    have h1 : T.sum (fun n => (n : ℝ))
        ≤ (B * (X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 3) / (c ^ 2 / (Real.log (X : ℝ)) ^ 2) :=
      (le_div_iff₀ hc2pos).mpr (by rw [mul_comm]; exact hq)
    have h2 : (B * (X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 3) / (c ^ 2 / (Real.log (X : ℝ)) ^ 2)
        = C * (X : ℝ) ^ 2 / Real.log (X : ℝ) := by
      rw [hCdef]
      field_simp
    rwa [h2] at h1
  -- conclude
  rcases Nat.eq_zero_or_pos T.card with h0 | hpos
  · have hz : euExc X = 0 := by rw [heuExc, h0]
    rw [hz]
    push_cast
    have : (0:ℝ) ≤ ε * (X:ℝ) := by positivity
    linarith
  · have ht1 : (1 : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast hpos
    have hcard := card_pred_mul_le_two_sum T
    have hsq1 : ((T.card : ℝ) - 1) ^ 2 ≤ (T.card : ℝ) * ((T.card : ℝ) - 1) := by nlinarith
    have hstep : 2 * (C * (X : ℝ) ^ 2 / Real.log (X : ℝ)) ≤ (ε * (X : ℝ) / 2) ^ 2 := by
      have hdiv : 2 * C / Real.log (X : ℝ) ≤ 2 * C / (16 * C / ε ^ 2) := by
        refine div_le_div_of_nonneg_left (by positivity) (by positivity) hlogbig
      have hval : 2 * C / (16 * C / ε ^ 2) = ε ^ 2 / 8 := by
        field_simp
        ring
      have hX2 : (0:ℝ) ≤ (X : ℝ) ^ 2 := by positivity
      have h1 : 2 * C / Real.log (X : ℝ) * (X : ℝ) ^ 2 ≤ ε ^ 2 / 8 * (X : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right (le_trans hdiv hval.le) hX2
      have h2 : 2 * (C * (X : ℝ) ^ 2 / Real.log (X : ℝ)) = 2 * C / Real.log (X : ℝ) * (X : ℝ) ^ 2 := by
        field_simp
      have h3 : ε ^ 2 / 8 * (X : ℝ) ^ 2 ≤ (ε * (X : ℝ) / 2) ^ 2 := by
        have hεXnn : (0:ℝ) ≤ ε * (X : ℝ) := by positivity
        nlinarith
      rw [h2]
      linarith
    have hkey : ((T.card : ℝ) - 1) ^ 2 ≤ (ε * (X : ℝ) / 2) ^ 2 := by linarith
    have hb : (0:ℝ) ≤ ε * (X : ℝ) / 2 := by positivity
    have hle : (T.card : ℝ) - 1 ≤ ε * (X : ℝ) / 2 := le_of_sq_le_sq hkey hb
    have hfin : (euExc X : ℝ) = (T.card : ℝ) := by rw [heuExc]
    rw [hfin]
    linarith

private theorem euExc_mono {X Y : ℕ} (h : X ≤ Y) : euExc X ≤ euExc Y := by
  classical
  unfold euExc
  refine Finset.card_le_card ?_
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
  exact ⟨⟨hn.1.1, le_trans hn.1.2 h⟩, hn.2⟩

/-- LEAF 4, from the powers of two to every `X`.  If the exceptions at `2 ^ k` are below
`epsilon * 2 ^ k` for all large `k`, then the exceptions at every `X` are below `epsilon * X` for
all large `X`: `euExc` is monotone, and for `1 ≤ X` there is `k` with `2 ^ k ≤ X < 2 ^ (k+1)`, so
`euExc X ≤ euExc (2 ^ (k+1)) ≤ (epsilon / 2) * 2 ^ (k+1) ≤ epsilon * X`.  The bound at `X = 0` and
`X = 1` is covered by taking the threshold large. -/
theorem leaf_dyadic_to_all_X
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in Filter.atTop, (euExc (2 ^ k) : ℝ) ≤ ε * ((2 ^ k : ℕ) : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℕ in Filter.atTop, (euExc X : ℝ) ≤ ε * X := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp (h (ε / 2) hε2)
  rw [Filter.eventually_atTop]
  refine ⟨2 ^ K, fun X hX => ?_⟩
  have hXpos : 0 < X := lt_of_lt_of_le (by positivity : (0 : ℕ) < 2 ^ K) hX
  have hXne : X ≠ 0 := by omega
  set k := Nat.log 2 X with hk
  have h1 : 2 ^ k ≤ X := Nat.pow_log_le_self 2 hXne
  have h2 : X < 2 ^ (k + 1) := by
    simpa [← hk] using Nat.lt_pow_succ_log_self (b := 2) (by norm_num) X
  have hKle : K ≤ k := by
    have h3 : 2 ^ K < 2 ^ (k + 1) := lt_of_le_of_lt hX h2
    have h4 : K < k + 1 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h3
    omega
  have hstep : euExc X ≤ euExc (2 ^ (k + 1)) := euExc_mono (le_of_lt h2)
  have hb : (euExc (2 ^ (k + 1)) : ℝ) ≤ (ε / 2) * ((2 ^ (k + 1) : ℕ) : ℝ) := hK (k + 1) (by omega)
  have hcast : ((2 ^ (k + 1) : ℕ) : ℝ) = 2 * ((2 ^ k : ℕ) : ℝ) := by
    rw [pow_succ]
    push_cast
    ring
  have hX' : ((2 ^ k : ℕ) : ℝ) ≤ (X : ℝ) := by exact_mod_cast h1
  calc (euExc X : ℝ) ≤ (euExc (2 ^ (k + 1)) : ℝ) := by exact_mod_cast hstep
    _ ≤ (ε / 2) * ((2 ^ (k + 1) : ℕ) : ℝ) := hb
    _ = ε * ((2 ^ k : ℕ) : ℝ) := by rw [hcast]; ring
    _ ≤ ε * (X : ℝ) := by nlinarith

/-- The sealed statement of `route_euler_almost_all`, assembled from the four leaves above. -/
theorem route_euler_almost_all_split :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℕ in Filter.atTop, (euExc X : ℝ) ≤ ε * X := by
  refine leaf_dyadic_to_all_X ?_
  intro ε hε
  obtain ⟨R, -, hR⟩ := leaf_representation_multiplicity
  obtain ⟨m, B, c, hB, hc, hmain, hvar⟩ := leaf_circle_method_variance R hR
  exact leaf_exception_count_dyadic R m B c hB hc hR hmain hvar ε hε

end LeanLab.OpenProblems.State1612
