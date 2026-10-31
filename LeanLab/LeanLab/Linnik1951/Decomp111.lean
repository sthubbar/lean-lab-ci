/-
P0093 pages 154 and 168 to 169. Decomposition of the lab's GRH existence statement.
AI wrote the Lean code. Binary Goldbach is open.
The circle method error remains a cited input. The Romanov input is proved in SecondMoment111.
-/
import LeanLab.Linnik1951.Conventions
import LeanLab.Perelli1996.Sing

namespace LeanLab.Linnik1951

open LeanLab.Linnik LeanLab.DERZ1997
open Finset

/-- Ordered representations in P0093 equation 2.1, page 154.
The finite bounds lose no representations because each summand is at most N. -/
noncomputable def representationCount111 (k N : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter fun t : Fin (N + 1) × Fin (N + 1) × (Fin k → Fin (N + 1)) =>
    (t.1.val).Prime ∧ (t.2.1.val).Prime ∧ (∀ i, 1 ≤ (t.2.2 i).val) ∧
      N = t.1.val + t.2.1.val + ∑ i, 2 ^ (t.2.2 i).val).card

/-- Singular series in P0093 page 168, equation 10.6. -/
noncomputable def singularSeries111 (n : ℕ) : ℝ :=
  ∏' p : Nat.Primes, if (p : ℕ) ∣ n then
    1 + 1 / (((p : ℕ) : ℝ) - 1) else 1 - 1 / (((p : ℕ) : ℝ) - 1) ^ 2

/-- Main term in P0093 page 168 after equation 10.7, with multiplicity of exponent tuples. -/
noncomputable def mainTerm111 (k N : ℕ) : ℝ := by
  classical
  exact ∑ ν ∈ (Finset.univ.filter fun ν : Fin k → Fin (N + 1) =>
    (∀ i, 1 ≤ (ν i).val) ∧ 2 ≤ N - ∑ i, 2 ^ (ν i).val ∧
      Even (N - ∑ i, 2 ^ (ν i).val)),
    singularSeries111 (N - ∑ i, 2 ^ (ν i).val) *
      (N - ∑ i, 2 ^ (ν i).val : ℕ) / Real.log (N - ∑ i, 2 ^ (ν i).val : ℕ) ^ 2

/-- The positive scale in P0093 Section 11, page 169. -/
noncomputable def scale111 (k N : ℕ) : ℝ :=
  N * (Real.log N / Real.log 2) ^ (k - 2)

/-- LEAF. P0093 page 154, equation 2.1. A positive count gives a representation. -/
theorem representation_of_count_pos111 {k N : ℕ} (h : 0 < representationCount111 k N) :
    LinnikExact k N := by
  classical
  unfold representationCount111 at h
  obtain ⟨t, ht⟩ := Finset.card_pos.mp h
  obtain ⟨_, hp, hq, hν, heq⟩ := Finset.mem_filter.mp ht
  exact ⟨t.1.val, t.2.1.val, hp, hq, fun i => (t.2.2 i).val, hν, heq⟩

/-- P0093 page 154, equation 2.1. No representation is lost by the finite bounds. -/
theorem count_pos_of_representation111 {k N : ℕ} (h : LinnikExact k N) : 0 < representationCount111 k N := by
  classical
  obtain ⟨p, q, hp, hq, ν, hν, hN⟩ := h
  have hpN : p < N + 1 := by omega
  have hqN : q < N + 1 := by omega
  have hνN : ∀ i, ν i < N + 1 := by
    intro i
    have hi : 2 ^ ν i ≤ ∑ j, 2 ^ ν j := Finset.single_le_sum (f := fun j : Fin k => 2 ^ ν j) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    have hpow : ν i < 2 ^ ν i := Nat.lt_two_pow_self
    omega
  unfold representationCount111
  apply Finset.card_pos.mpr
  refine ⟨(⟨p, hpN⟩, ⟨q, hqN⟩, fun i => ⟨ν i, hνN i⟩), ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hp, hq, hν, hN⟩

/-- LEAF. P0093 Section 10, page 168 after equation 10.7.
This leaf includes the analytic work of Sections 3 to 10 and Romanov 1940,
reference 4, used by Lemma 3 on page 162. The geometric exponent is weakened
from k minus 1 to k minus 2 using zero less than eta less than one. -/
theorem error_bound111 (hG : GRH) :
    ∃ C η : ℝ, 0 < C ∧ 0 < η ∧ η < 1 ∧
      ∀ k : ℕ, 3 ≤ k → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
        |(representationCount111 k N : ℝ) - mainTerm111 k N| ≤
          5 * C * scale111 k N * (1 - η) ^ (k - 2) := by
  sorry

/-- P0093 page 168 following equation 10.6. The singular series is at least one
at every positive even residual, by the existing lab Euler product proof. -/
theorem one_le_singularSeries111 {n : ℕ} (hn : Even n) (hn2 : 2 ≤ n) :
    1 ≤ singularSeries111 n := by
  change 1 ≤ LeanLab.Perelli1996.Sing n
  exact LeanLab.Perelli1996.one_le_sing hn (by omega)

/-- P0093 Section 11, page 168. Every tuple in a small exponent box has a positive even residual. -/
theorem cutoff_residual111 {N k L : ℕ} (ν : Fin k → ℕ) (hcut : k * 2 ^ L + 2 ≤ N)
    (hν : ∀ i, 1 ≤ ν i) (hL : ∀ i, ν i ≤ L) (hN : Even N) :
    2 ≤ N - ∑ i, 2 ^ ν i ∧ Even (N - ∑ i, 2 ^ ν i) := by
  have hsum : ∑ i, 2 ^ ν i ≤ k * 2 ^ L := by
    calc
      _ ≤ ∑ _ : Fin k, 2 ^ L := by
        apply Finset.sum_le_sum
        intro i hi
        exact Nat.pow_le_pow_right (by norm_num) (hL i)
      _ = k * 2 ^ L := by simp
  have htwo : 2 ∣ ∑ i, 2 ^ ν i := by
    apply Finset.dvd_sum
    intro i hi
    exact dvd_pow_self 2 (by have := hν i; omega)
  refine ⟨by omega, ?_⟩
  exact even_iff_two_dvd.mpr (Nat.dvd_sub (even_iff_two_dvd.mp hN) htwo)

/-- P0093 Section 11, page 168. A common logarithmic denominator bounds each positive even summand. -/
theorem main_weight_lower111 {n N : ℕ} (hn : 2 ≤ n) (hnN : n ≤ N) (hev : Even n) :
    (n : ℝ) / Real.log N ^ 2 ≤ singularSeries111 n * n / Real.log n ^ 2 := by
  have hnr : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hln := Real.log_pos hnr
  have hlN := Real.log_pos hNr
  have hlog : Real.log n ≤ Real.log N := Real.log_le_log (by linarith) (by exact_mod_cast hnN)
  have hsq : Real.log n ^ 2 ≤ Real.log N ^ 2 := by nlinarith
  have hsing := one_le_singularSeries111 hev hn
  calc
    _ ≤ (n : ℝ) / Real.log n ^ 2 :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) (sq_pos_of_pos hln) hsq
    _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith [Nat.cast_nonneg (α := ℝ) n]) (sq_nonneg _)

/-- P0093 Section 11, pages 168 and 169. The full exponent box contributes a uniform lower sum. -/
theorem main_box_lower111 (N k L : ℕ) (hN : Even N) (hLN : L ≤ N) (hcut : k * 2 ^ L + 2 ≤ N)
 :
    (L : ℝ) ^ k * ((N - k * 2 ^ L : ℕ) : ℝ) / Real.log N ^ 2 ≤ mainTerm111 k N := by
  classical
  let e : (Fin k → Fin L) → (Fin k → Fin (N + 1)) :=
    fun ν i => ⟨(ν i).val + 1, by have := (ν i).isLt; omega⟩
  let t := univ.filter fun ν : Fin k → Fin (N + 1) =>
    (∀ i, 1 ≤ (ν i).val) ∧ 2 ≤ N - ∑ i, 2 ^ (ν i).val ∧ Even (N - ∑ i, 2 ^ (ν i).val)
  let w : (Fin k → Fin (N + 1)) → ℝ := fun ν =>
    singularSeries111 (N - ∑ i, 2 ^ (ν i).val) *
      (N - ∑ i, 2 ^ (ν i).val : ℕ) / Real.log (N - ∑ i, 2 ^ (ν i).val : ℕ) ^ 2
  let B : ℝ := ((N - k * 2 ^ L : ℕ) : ℝ) / Real.log N ^ 2
  have hsum (ν : Fin k → Fin L) : ∑ i, 2 ^ ((e ν i).val) ≤ k * 2 ^ L := by
    calc
      _ ≤ ∑ _ : Fin k, 2 ^ L := by
        apply sum_le_sum
        intro i hi
        apply Nat.pow_le_pow_right (by norm_num)
        dsimp [e]
        have := (ν i).isLt
        omega
      _ = _ := by simp
  have ht (ν : Fin k → Fin L) : e ν ∈ t := by
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    exact ⟨fun i => by dsimp [e]; omega,
      cutoff_residual111 (fun i => (e ν i).val) hcut
        (fun i => by dsimp [e]; omega)
        (fun i => by dsimp [e]; have := (ν i).isLt; omega) hN⟩
  have hcmp : ∑ _ : Fin k → Fin L, B ≤ mainTerm111 k N := by
    change _ ≤ ∑ ν ∈ t, w ν
    apply sum_le_sum_of_injOn e
    · intro a ha b hb hab
      funext i
      have h := congrArg (fun f => (f i).val) hab
      apply Fin.ext
      dsimp [e] at h
      omega
    · intro z hz
      obtain ⟨ν, hν, rfl⟩ := mem_image.mp hz
      exact ht ν
    · intro ν hν
      have hmem := (mem_filter.mp (ht ν)).2
      have hres : N - k * 2 ^ L ≤ N - ∑ i, 2 ^ (e ν i).val := by have := hsum ν; omega
      have hresr : ((N - k * 2 ^ L : ℕ) : ℝ) ≤ (N - ∑ i, 2 ^ (e ν i).val : ℕ) := by exact_mod_cast hres
      exact (div_le_div_of_nonneg_right hresr (sq_nonneg _)).trans
        (main_weight_lower111 hmem.2.1 (Nat.sub_le _ _) hmem.2.2)
    · intro ν hν hn
      have hmem := (mem_filter.mp hν).2
      have hs := one_le_singularSeries111 hmem.2.2 hmem.2.1
      dsimp [w]
      positivity
  simpa [B, mul_div_assoc] using hcmp

/-- P0093 Section 11, page 169. Bernoulli bounds the power loss from a bounded cutoff gap. -/
theorem power_lower_of_gap111 (k : ℕ) (t L D : ℝ) (ht : 0 < t) (hL : 0 ≤ L)
    (hgap : t - L ≤ D) (hlarge : 2 * k * D ≤ t) : t ^ k / 2 ≤ L ^ k := by
  have hratio : 0 ≤ L / t := div_nonneg hL ht.le
  have hbern := one_add_mul_le_pow (show -2 ≤ L / t - 1 by linarith) k
  have hmid : (1 / 2 : ℝ) ≤ 1 + k * (L / t - 1) := by
    have hid : 1 + k * (L / t - 1) = (t + k * (L - t)) / t := by field_simp
    rw [hid]
    apply (le_div_iff₀ ht).mpr
    have hh := mul_le_mul_of_nonneg_left hgap (Nat.cast_nonneg (α := ℝ) k)
    nlinarith
  have hbern' : (1 / 2 : ℝ) ≤ (L / t) ^ k := by
    have hid : 1 + (L / t - 1) = L / t := by ring
    rw [hid] at hbern
    exact hmid.trans hbern
  rw [div_pow, le_div_iff₀ (pow_pos ht k)] at hbern'
  nlinarith

/-- P0093 Section 11, pages 168 and 169. An explicit logarithmic threshold suffices for the main lower bound. -/
theorem main_lower_at111 (k N : ℕ) (hk : 3 ≤ k) (hN : 4 ≤ N) (hev : Even N)
    (hlarge : 2 * (k : ℝ) * (Real.log (2 * (k : ℝ)) / Real.log 2 + 1) ≤
      Real.log N / Real.log 2) :
    (1 / (4 * Real.log 2 ^ 2)) * scale111 k N ≤ mainTerm111 k N := by
  let t := Real.log N / Real.log 2
  let d := Real.log (2 * (k : ℝ)) / Real.log 2
  let L := ⌊t - d⌋₊
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hNR : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hkp : (0 : ℝ) < k := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have ht : 0 < t := div_pos hlogN hl2
  have hd : 0 ≤ d := div_nonneg (Real.log_nonneg (by linarith)) hl2.le
  have htd : 0 ≤ t - d := by
    change 2 * (k : ℝ) * (d + 1) ≤ t at hlarge
    nlinarith
  have hLf : (L : ℝ) ≤ t - d := Nat.floor_le htd
  have hX : 0 < (N : ℝ) / (2 * k) := div_pos hNp (by positivity)
  have hpow : (2 : ℝ) ^ L ≤ (N : ℝ) / (2 * k) := by
    apply (Real.log_le_log_iff (pow_pos (by norm_num) L) hX).mp
    rw [Real.log_pow, Real.log_div hNp.ne' (by positivity : 2 * (k : ℝ) ≠ 0)]
    have h := mul_le_mul_of_nonneg_right hLf hl2.le
    dsimp [t, d] at h
    simpa only [sub_mul, div_mul_cancel₀ _ hl2.ne'] using h
  have hdoubleR : (2 : ℝ) * ((k : ℝ) * 2 ^ L) ≤ N := by
    have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * k)).mp hpow
    nlinarith
  have hdouble : 2 * (k * 2 ^ L) ≤ N := by exact_mod_cast hdoubleR
  have hcut : k * 2 ^ L + 2 ≤ N := by omega
  have hpowN : (2 : ℝ) ^ L ≤ N := by nlinarith [pow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) L]
  have hpowNnat : 2 ^ L ≤ N := by exact_mod_cast hpowN
  have hLN : L ≤ N := (Nat.lt_two_pow_self.trans_le hpowNnat).le
  have hgap : t - (L : ℝ) ≤ d + 1 := by
    have h := Nat.lt_floor_add_one (t - d)
    change t - d < (L : ℝ) + 1 at h
    linarith
  have hLpow := power_lower_of_gap111 k t L (d + 1) ht (Nat.cast_nonneg _) hgap hlarge
  have hres : (N : ℝ) / 2 ≤ ((N - k * 2 ^ L : ℕ) : ℝ) := by
    rw [Nat.cast_sub (show k * 2 ^ L ≤ N by omega)]
    push_cast
    nlinarith
  have hlogeq : Real.log N = t * Real.log 2 := by dsimp [t]; field_simp
  have htpow : t ^ k = t ^ (k - 2) * t ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  have hid : (1 / (4 * Real.log 2 ^ 2)) * scale111 k N * Real.log N ^ 2 =
      (t ^ k / 2) * ((N : ℝ) / 2) := by
    change (1 / (4 * Real.log 2 ^ 2)) * ((N : ℝ) * t ^ (k - 2)) * Real.log N ^ 2 = _
    rw [hlogeq, htpow]
    field_simp
    ring
  calc
    _ ≤ (L : ℝ) ^ k * ((N - k * 2 ^ L : ℕ) : ℝ) / Real.log N ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hlogN)).mpr
      rw [hid]
      exact mul_le_mul hLpow hres (by positivity) (by positivity)
    _ ≤ _ := main_box_lower111 N k L hev hLN hcut

/-- LEAF. P0093 Section 11, pages 168 and 169. The main term has a uniform
positive lower coefficient for each fixed k and all sufficiently large even N.
The singular series lower bound is the assertion following equation 10.6. -/
theorem main_lower111 :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 3 ≤ k → ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 < N → c * scale111 k N ≤ mainTerm111 k N := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 / (4 * Real.log 2 ^ 2), by positivity, ?_⟩
  intro k hk
  let T := 2 * (k : ℝ) * (Real.log (2 * (k : ℝ)) / Real.log 2 + 1)
  obtain ⟨B, hB⟩ := exists_nat_gt (Real.exp (T * Real.log 2))
  refine ⟨max 4 B, ?_⟩
  intro N hev hN
  have hNB : B < N := lt_of_le_of_lt (le_max_right _ _) hN
  have h4 : 4 ≤ N := by have := le_max_left 4 B; omega
  have hNB' : (B : ℝ) < N := by exact_mod_cast hNB
  have hlarge : T ≤ Real.log N / Real.log 2 := by
    apply (le_div_iff₀ hl2).mpr
    have hh := Real.log_le_log (Real.exp_pos (T * Real.log 2)) (hB.trans hNB').le
    rwa [Real.log_exp] at hh
  exact main_lower_at111 k N hk h4 hev hlarge

/-- LEAF. P0093 Section 11, page 169. Choose a fixed k so the geometric error
coefficient is smaller than the positive main coefficient. -/
theorem choose_exponent111 {C c η : ℝ} (hC : 0 < C) (hc : 0 < c)
    (hη : 0 < η) (hη1 : η < 1) :
    ∃ k : ℕ, 3 ≤ k ∧ 5 * C * (1 - η) ^ (k - 2) < c := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hc (by positivity : 0 < 5 * C))
    (show 1 - η < 1 by linarith)
  refine ⟨n + 3, by omega, ?_⟩
  have hp : (1 - η) ^ (n + 3 - 2) ≤ (1 - η) ^ n :=
    pow_le_pow_of_le_one (by linarith) (by linarith) (by omega)
  have hh : (1 - η) ^ (n + 3 - 2) < c / (5 * C) := hp.trans_lt hn
  simpa only [mul_comm] using (lt_div_iff₀ (by positivity : 0 < 5 * C)).mp hh

/-- LEAF. P0093 page 169. The scale is positive once N is larger than one. -/
theorem scale_pos111 (k N : ℕ) (hN : 1 < N) : 0 < scale111 k N := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  exact mul_pos (by exact_mod_cast (show 0 < N by omega))
    (pow_pos (div_pos (Real.log_pos hNr) (Real.log_pos (by norm_num))) _)

/-- LEAF. P0093 page 169. A main term larger than its absolute error gives
positive representation count. This is the real arithmetic step. -/
theorem positive_of_error111 {q m s a c : ℝ} (hs : 0 < s) (hac : a < c)
    (hm : c * s ≤ m) (he : |q - m| ≤ a * s) : 0 < q := by
  have h := (abs_le.mp he).1
  nlinarith

/-- P0093 pages 154 and 168 to 169. Assembly of the exact lab statement.
CONDITIONAL only on error_bound111. The main lower bound is proved. -/
theorem linnik1951_decomposed111 : GRH → ∃ K, AllLargeEven (LinnikAtMost K) := by
  intro hG
  obtain ⟨C, η, hC, hη, hη1, he⟩ := error_bound111 hG
  obtain ⟨c, hc, hm⟩ := main_lower111
  obtain ⟨k, hk, hkc⟩ := choose_exponent111 hC hc hη hη1
  obtain ⟨Ne, he⟩ := he k hk
  obtain ⟨Nm, hm⟩ := hm k hk
  refine ⟨k, max 1 (max Ne Nm), ?_⟩
  intro N hev hN
  have h1 : 1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hNe : Ne < N := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNm : Nm < N := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have he' := he N hev hNe
  have hpos : 0 < (representationCount111 k N : ℝ) :=
    positive_of_error111 (scale_pos111 k N h1) hkc (hm N hev hNm) (by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using he')
  exact atMost_of_exact (representation_of_count_pos111 (by exact_mod_cast hpos))

end LeanLab.Linnik1951
