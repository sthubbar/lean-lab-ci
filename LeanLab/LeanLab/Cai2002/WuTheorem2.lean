/-
J. Wu, Théorèmes généralisés de Bombieri-Vinogradov dans les petits intervalles,
Quart. J. Math. Oxford 44 (1993), 109 to 128, papers/Wu1993.pdf, Théorème 2, display 1.7,
page 111; this is the result Cai 2002 quotes as Lemma 4 on page 599.

`WuTheorem2Stmt` states display 1.7 as printed, with Wu's names: g(l) a real arithmetic
function with hypothesis 1.4, Σ_{l ≤ x} |g(l)|²/l ≪ 𝓛^λ, 𝓛 = log x;
H₁(z, h, q, a, l) = π(z + h; q, a, l) - π(z; q, a, l) - (1/φ(q)) ∫_{z/l}^{(z+h)/l} dt / log t,
where π(z; q, a, l) counts primes p with l p ≤ z and l p ≡ a mod q, so H₁ counts
z < l p ≤ z + h; the sum over q ≤ Q = x^(θ - 1/2) 𝓛^(-B) of the max over (a, q) = 1, h ≤ y,
x/2 < z ≤ x of the sum over l ≤ L = x^((5θ - 3)/2 - ε), (l, q) = 1, is ≪ y 𝓛^(-A),
for 3/5 + ε ≤ θ ≤ 1 and y = x^θ.
The maxima are written as a bound for every choice of a, h and z at each q, and h ≥ 0 is
asked, which only weakens the statement. The implied constant ≪ is read as depending only
on θ, ε, λ, A and the implied constant C of hypothesis 1.4, uniformly in g. Wu's proof
supports this: g enters only through |g(l)| and hypothesis 1.4, pages 117 and 118 by
Cauchy-Schwarz with 1.4, and page 127 by Lemma 2.6 with 1.4. B depends only on A and λ,
B = 3A + λ + 34 on page 112; here B is only asserted to exist.

`wuUniform_of_wuTheorem2` proves the lab's `WuUniformStmt` from it. Wu's interval
z < l p ≤ z + h has the same open left end as `switchedLocalCount337`, so the only
difference is the primes r dividing N, at most three of them above N^0.3.
No sorry is used in this file. AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.Cai2002.WuLiteral

open Filter Finset Real
open scoped Topology
noncomputable section
namespace LeanLab.Cai2002

/-- H₁(z, h, q, a, l) of Wu 1993 Théorème 2, page 111: the primes p with z < l p ≤ z + h
and l p ≡ a mod q, minus (1/φ(q)) ∫_{z/l}^{(z+h)/l} dt / log t. For l ≥ 1 every such p is at
most z + h, so the finite range loses nothing. -/
def wuH1 (z h : ℝ) (q a l : ℕ) : ℝ :=
  ((((range (⌊z + h⌋₊ + 1)).filter (fun p => p.Prime ∧ z < ((l * p : ℕ) : ℝ) ∧
      ((l * p : ℕ) : ℝ) ≤ z + h ∧ l * p ≡ a [MOD q])).card : ℕ) : ℝ) -
    1 / (q.totient : ℝ) * ∫ t in z / l..(z + h) / l, 1 / log t

/-- CITED STATEMENT, not proved. Wu 1993, Théorème 2, display 1.7, page 111, for real g,
with the implied constant uniform in g given the constant C of hypothesis 1.4. -/
def WuTheorem2Stmt : Prop :=
  ∀ θ ε lam C A : ℝ, 0 < ε → 3 / 5 + ε ≤ θ → θ ≤ 1 → 0 < lam → 0 < C → 0 < A →
    ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧ ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x →
    ∀ g : ℕ → ℝ,
      (∀ u : ℝ, 2 ≤ u → ∑ l ∈ Icc 1 ⌊u⌋₊, |g l| ^ 2 / l ≤ C * log u ^ lam) →
    ∀ (a : ℕ → ℕ) (h z : ℕ → ℝ), (∀ q, (a q).Coprime q) →
      (∀ q, 0 ≤ h q ∧ h q ≤ x ^ θ) → (∀ q, x / 2 < z q ∧ z q ≤ x) →
      ∑ q ∈ Icc 1 ⌊x ^ (θ - 1 / 2) / log x ^ B⌋₊,
        |∑ l ∈ (Icc 1 ⌊x ^ ((5 * θ - 3) / 2 - ε)⌋₊).filter (fun l => l.Coprime q),
          g l * wuH1 (z q) (h q) q (a q) l| ≤ K * x ^ θ / log x ^ A

/-- The prime count of H₁ at z = N - N^0.95, h = N^0.95, l = e, a = N mod d. -/
def wuCount1 (N d e : ℕ) : Finset ℕ :=
  (range (N + 1)).filter (fun p => p.Prime ∧ (N : ℝ) - (N : ℝ) ^ (0.95 : ℝ) < ((e * p : ℕ) : ℝ) ∧
    ((e * p : ℕ) : ℝ) ≤ N ∧ e * p ≡ N % d [MOD d])

/-- The primes r dividing N, which H₁ counts and `switchedLocalCount337` does not. -/
def wuBadDvd1 (N d e : ℕ) : Finset ℕ :=
  (range (N + 1)).filter (fun r => r.Prime ∧ r ∣ N ∧
    (N : ℝ) - (N : ℝ) ^ (0.95 : ℝ) < ((e * r : ℕ) : ℝ) ∧ e * r ≤ N ∧ d ∣ N - e * r)

theorem intervalIntegrable_inv_log (X : ℝ) (hX : 2 ≤ X) :
    IntervalIntegrable (fun t => 1 / log t) MeasureTheory.volume 2 X := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_const.div (continuousOn_log.mono ?_)
  · intro t ht
    rw [Set.uIcc_of_le hX] at ht
    exact (log_pos (by linarith [ht.1])).ne'
  · intro t ht
    rw [Set.uIcc_of_le hX] at ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith [ht.1]

theorem wuH1_switched (N d e : ℕ)
    (h2 : 2 ≤ ((N : ℝ) - (N : ℝ) ^ (0.95 : ℝ)) / e) :
    wuH1 ((N : ℝ) - (N : ℝ) ^ (0.95 : ℝ)) ((N : ℝ) ^ (0.95 : ℝ)) d (N % d) e =
      ((wuCount1 N d e).card : ℝ) - switchedLiTerm337 N e / d.totient := by
  have hy : (0 : ℝ) ≤ (N : ℝ) ^ (0.95 : ℝ) := by positivity
  have h2' : 2 ≤ (N : ℝ) / e := by
    refine h2.trans (div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _))
  unfold wuH1 wuCount1 switchedLiTerm337 li118
  rw [sub_add_cancel, Nat.floor_natCast,
    ← intervalIntegral.integral_interval_sub_left (intervalIntegrable_inv_log _ h2')
      (intervalIntegrable_inv_log _ h2)]
  ring

/-- The strict count is at most the count of H₁, which exceeds it by at most the primes
dividing N. -/
theorem wuCount1_bounds (N d e : ℕ) (hy : (N : ℝ) ^ (0.95 : ℝ) < N) :
    switchedLocalCount337 N e d ≤ (wuCount1 N d e).card ∧
      (wuCount1 N d e).card ≤ switchedLocalCount337 N e d + (wuBadDvd1 N d e).card := by
  unfold switchedLocalCount337
  constructor
  · apply card_le_card
    intro r hr
    simp only [wuCount1, mem_filter, mem_range] at hr ⊢
    obtain ⟨hrN, hp, _, h1, h2, h3⟩ := hr
    exact ⟨by omega, hp, h1, by exact_mod_cast h2.le, (modEq_mod_iff_dvd N d _ h2.le).2 h3⟩
  · have hsub : wuCount1 N d e ⊆ ((range N).filter (fun r => r.Prime ∧ r.Coprime N ∧
        (N : ℝ) - (N : ℝ) ^ (0.95 : ℝ) < (e * r : ℕ) ∧ e * r < N ∧ d ∣ N - e * r)) ∪
        wuBadDvd1 N d e := by
      intro p hp
      simp only [wuCount1, mem_filter] at hp
      obtain ⟨hpN, hpp, h1, h2, h3⟩ := hp
      have hle : e * p ≤ N := by exact_mod_cast h2
      have hdv := (modEq_mod_iff_dvd N d _ hle).1 h3
      simp only [mem_union, wuBadDvd1, mem_filter, mem_range]
      by_cases hc : p.Coprime N
      · have hne : e * p ≠ N := by
          intro heq
          exact (Nat.Prime.coprime_iff_not_dvd hpp).1 hc ⟨e, by rw [← heq, mul_comm]⟩
        have hlt : e * p < N := lt_of_le_of_ne hle hne
        have he : 0 < e := by
          rcases Nat.eq_zero_or_pos e with h0 | h0
          · rw [h0, zero_mul, Nat.cast_zero] at h1; linarith
          · exact h0
        have hpN' : p < N := lt_of_le_of_lt (Nat.le_mul_of_pos_left p he) hlt
        exact Or.inl ⟨hpN', hpp, hc, h1, hlt, hdv⟩
      · have : p ∣ N := by
          by_contra hn; exact hc ((Nat.Prime.coprime_iff_not_dvd hpp).2 hn)
        exact Or.inr ⟨mem_range.mp hpN, hpp, this, h1, hle, hdv⟩
    calc (wuCount1 N d e).card ≤ _ := card_le_card hsub
      _ ≤ _ := card_union_le _ _

/-- For r dividing N and d coprime to r, the e with N - y < e r ≤ N and d ∣ N - e r number
at most (y / r) / d + 1, through k = N / r - e, a multiple of d in [0, y / r]. -/
theorem card_shift_dvd_le1 (r N d : ℕ) (hr : r ∣ N) (hd : d.Coprime r) (y : ℝ) (hy0 : 0 ≤ y)
    (hr0 : 0 < r) (S : Finset ℕ)
    (hS : ∀ e ∈ S, (N : ℝ) - y < ((e * r : ℕ) : ℝ) ∧ e * r ≤ N ∧ d ∣ N - e * r) :
    (S.card : ℝ) ≤ (y / r) / d + 1 := by
  obtain ⟨n, rfl⟩ := hr
  have hen : ∀ e ∈ S, e ≤ n := by
    intro e he
    have := (hS e he).2.1
    by_contra h; rw [not_le] at h; nlinarith [Nat.mul_lt_mul_of_pos_left h hr0]
  have hinj : Set.InjOn (fun e => n - e) S := by
    intro a ha b hb hab
    have := hen a ha; have := hen b hb
    simp only at hab; omega
  have hmap : ∀ e ∈ S, (fun e => n - e) e ∈
      insert 0 ((Ioc 0 ⌊y / r⌋₊).filter (fun k => d ∣ k)) := by
    intro e he
    obtain ⟨h1, h2, h3⟩ := hS e he
    have hle := hen e he
    simp only [mem_insert, mem_filter, mem_Ioc]
    have hsub : r * n - e * r = r * (n - e) := by
      rw [Nat.mul_sub, mul_comm e r]
    by_cases h0 : n - e = 0
    · exact Or.inl h0
    · refine Or.inr ⟨⟨by omega, ?_⟩, ?_⟩
      · apply Nat.le_floor
        rw [le_div_iff₀ (by exact_mod_cast hr0)]
        have hcast : ((r * (n - e) : ℕ) : ℝ) = ((r * n : ℕ) : ℝ) - ((e * r : ℕ) : ℝ) := by
          rw [← hsub, Nat.cast_sub (by nlinarith)]
        have : ((n - e : ℕ) : ℝ) * r = ((r * (n - e) : ℕ) : ℝ) := by push_cast; ring
        rw [this, hcast]; linarith
      · rw [hsub] at h3
        exact hd.dvd_of_dvd_mul_left h3
  have hc := Finset.card_le_card_of_injOn _ hmap hinj
  have hc2 := hc.trans (card_insert_le _ _)
  rw [Nat.Ioc_filter_dvd_card_eq_div] at hc2
  calc (S.card : ℝ) ≤ ((⌊y / r⌋₊ / d : ℕ) : ℝ) + 1 := by exact_mod_cast hc2
    _ ≤ (⌊y / r⌋₊ : ℝ) / d + 1 := by gcongr; exact Nat.cast_div_le
    _ ≤ (y / r) / d + 1 := by
        gcongr
        exact Nat.floor_le (div_nonneg hy0 (Nat.cast_nonneg _))

/-- The pairs with r dividing N: at most 3 ((y / T) / d + 1) over all e in E. -/
theorem sum_wuBadDvd1_le (N d : ℕ) (E : Finset ℕ) (hd : N.Coprime d) (hN : N ≠ 0)
    (T : ℝ) (hT : 1 ≤ T) (hTN : (N : ℝ) < T ^ 4)
    (hlarge : ∀ e ∈ E, ∀ r : ℕ,
      (N : ℝ) - (N : ℝ) ^ (0.95 : ℝ) ≤ ((e * r : ℕ) : ℝ) → T ≤ r) :
    ∑ e ∈ E, ((wuBadDvd1 N d e).card : ℝ) ≤ 3 * (((N : ℝ) ^ (0.95 : ℝ) / T) / d + 1) := by
  have hy0 : (0 : ℝ) ≤ (N : ℝ) ^ (0.95 : ℝ) := by positivity
  set c := ((N : ℝ) ^ (0.95 : ℝ) / T) / d + 1
  have hc0 : 0 ≤ c := by positivity
  set R := N.primeFactors.filter (fun r : ℕ => T ≤ (r : ℝ))
  have hswap : ∑ e ∈ E, ((wuBadDvd1 N d e).card : ℝ) =
      ∑ r ∈ range (N + 1), ((E.filter (fun e => r.Prime ∧ r ∣ N ∧
        (N : ℝ) - (N : ℝ) ^ (0.95 : ℝ) < ((e * r : ℕ) : ℝ) ∧ e * r ≤ N ∧
          d ∣ N - e * r)).card : ℝ) := by
    simp only [wuBadDvd1, card_filter]
    push_cast
    exact sum_comm
  rw [hswap]
  calc _ ≤ ∑ r ∈ range (N + 1), (if r ∈ R then c else 0) := by
        apply sum_le_sum
        intro r _
        split_ifs with hr
        · simp only [R, mem_filter, Nat.mem_primeFactors] at hr
          obtain ⟨⟨hp, hrN, _⟩, hTr⟩ := hr
          have hdr : d.Coprime r := (Nat.Coprime.coprime_dvd_left hrN hd).symm
          refine (card_shift_dvd_le1 r N d hrN hdr _ hy0 hp.pos _ ?_).trans ?_
          · intro e he
            simp only [mem_filter] at he
            exact ⟨he.2.2.2.1, he.2.2.2.2.1, he.2.2.2.2.2⟩
          · have hT0 : 0 < T := by linarith
            have h1 := div_le_div_of_nonneg_left hy0 hT0 hTr
            have h2 := div_le_div_of_nonneg_right h1 (Nat.cast_nonneg (α := ℝ) d)
            simp only [c]
            linarith
        · apply le_of_eq
          norm_cast
          rw [card_eq_zero, filter_eq_empty_iff]
          rintro e he ⟨hp, hrN, hle, _⟩
          apply hr
          simp only [R, mem_filter, Nat.mem_primeFactors]
          exact ⟨⟨hp, hrN, hN⟩, hlarge e he r hle.le⟩
    _ = ((range (N + 1)).filter (· ∈ R)).card * c := by
        rw [← sum_filter, sum_const, nsmul_eq_mul]
    _ ≤ 3 * c := by
        gcongr
        have h1 : ((range (N + 1)).filter (· ∈ R)).card ≤ R.card :=
          card_le_card (fun r hr => (mem_filter.mp hr).2)
        have h2 := card_large_primeFactors_le N hN T hT hTN
        exact_mod_cast h1.trans h2

/-- One modulus: the lab remainder is at most the H₁ sum plus the bad count. -/
theorem swWu_le_wuH1 (N d : ℕ) (E : Finset ℕ) (hy : (N : ℝ) ^ (0.95 : ℝ) < N)
    (hE2 : ∀ e ∈ E, 2 ≤ ((N : ℝ) - (N : ℝ) ^ (0.95 : ℝ)) / e) :
    swWu337 N d E ≤
      |∑ e ∈ E.filter (fun e => e.Coprime d),
          wuH1 ((N : ℝ) - (N : ℝ) ^ (0.95 : ℝ)) ((N : ℝ) ^ (0.95 : ℝ)) d (N % d) e| +
        ∑ e ∈ E, ((wuBadDvd1 N d e).card : ℝ) := by
  unfold swWu337
  set E' := E.filter (fun e => e.Coprime d)
  have hsplit : (∑ e ∈ E', ((switchedLocalCount337 N e d : ℝ) -
        switchedLiTerm337 N e / d.totient)) =
      (∑ e ∈ E', wuH1 ((N : ℝ) - (N : ℝ) ^ (0.95 : ℝ)) ((N : ℝ) ^ (0.95 : ℝ)) d (N % d) e) -
        ∑ e ∈ E', (((wuCount1 N d e).card : ℝ) - switchedLocalCount337 N e d) := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro e he
    rw [wuH1_switched N d e (hE2 e (mem_filter.mp he).1)]
    ring
  have hnn : 0 ≤ ∑ e ∈ E', (((wuCount1 N d e).card : ℝ) - switchedLocalCount337 N e d) := by
    apply sum_nonneg
    intro e _
    have := (wuCount1_bounds N d e hy).1
    have : (switchedLocalCount337 N e d : ℝ) ≤ (wuCount1 N d e).card := by exact_mod_cast this
    linarith
  rw [hsplit]
  refine (abs_sub _ _).trans ?_
  rw [abs_of_nonneg hnn]
  gcongr
  calc _ ≤ ∑ e ∈ E', ((wuBadDvd1 N d e).card : ℝ) := by
        apply sum_le_sum
        intro e _
        have := (wuCount1_bounds N d e hy).2
        have : ((wuCount1 N d e).card : ℝ) ≤ (switchedLocalCount337 N e d : ℝ) +
            (wuBadDvd1 N d e).card := by exact_mod_cast this
        linarith
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)

/-- Hypothesis 1.4 of Wu with λ = 1 and C = 3 for any g with |g| ≤ 1. -/
theorem wu_hyp14_of_abs_le_one (g : ℕ → ℝ) (hg : ∀ n, |g n| ≤ 1) (u : ℝ) (hu : 2 ≤ u) :
    ∑ l ∈ Icc 1 ⌊u⌋₊, |g l| ^ 2 / l ≤ 3 * log u ^ (1 : ℝ) := by
  rw [rpow_one]
  have hfl : 1 ≤ ⌊u⌋₊ := Nat.le_floor (by push_cast; linarith)
  calc _ ≤ ∑ l ∈ Icc 1 ⌊u⌋₊, ((l : ℝ))⁻¹ := by
        apply sum_le_sum
        intro l _
        rw [div_eq_mul_inv]
        have h1 : |g l| ^ 2 ≤ 1 := by
          have := hg l
          have := abs_nonneg (g l)
          nlinarith
        have : (0 : ℝ) ≤ ((l : ℝ))⁻¹ := by positivity
        nlinarith
    _ ≤ 1 + log (⌊u⌋₊ : ℝ) := by
        have := harmonic_le_one_add_log ⌊u⌋₊
        rw [harmonic_eq_sum_Icc] at this
        push_cast at this
        exact this
    _ ≤ 1 + log u := by
        have := log_le_log (by exact_mod_cast (show 0 < ⌊u⌋₊ by omega) : (0 : ℝ) < ⌊u⌋₊)
          (Nat.floor_le (by linarith : (0 : ℝ) ≤ u))
        linarith
    _ ≤ 3 * log u := by
        have : log 2 ≤ log u := log_le_log (by norm_num) hu
        have := Real.log_two_gt_d9
        linarith

/-- The large N facts used below. -/
theorem wu2_eventually (A B : ℝ) (hB : 0 < B) :
    ∀ᶠ N : ℕ in atTop, 3 ≤ N ∧ 3 * (N : ℝ) ^ (0.95 : ℝ) ≤ N ∧
      2 * (N : ℝ) ^ ((2 / 3 : ℝ) + 0.3) ≤ N ∧ 4 * (N : ℝ) ^ (2 / 3 : ℝ) ≤ N ∧
      9 * log N ^ (A + 1) ≤ (N : ℝ) ^ (0.3 : ℝ) ∧
      (N : ℝ) ^ (0.25 : ℝ) ≤ sw2Level337 N B ∧ sw2Level337 N B ≤ (N : ℝ) ^ (0.45 : ℝ) := by
  have hpow (a c : ℝ) (ha : 0 < a) : ∀ᶠ N : ℕ in atTop, c ≤ (N : ℝ) ^ a :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop |>.eventually
      (eventually_ge_atTop c)
  have hlo := (isLittleO_log_rpow_rpow_atTop (A + 1) (by norm_num : (0 : ℝ) < 0.3)).bound
    (by norm_num : (0 : ℝ) < 1 / 9)
  have hlo' := tendsto_natCast_atTop_atTop.eventually hlo
  filter_upwards [eventually_ge_atTop 3, hpow 0.05 3 (by norm_num), hpow (1 / 30) 2 (by norm_num),
    hpow (1 / 3) 4 (by norm_num), hlo', sw2_level_bounds337 B hB]
    with N hN3 h05 h30 h3 hl hlev
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  refine ⟨hN3, ?_, ?_, ?_, ?_, hlev⟩
  · have : (N : ℝ) = (N : ℝ) ^ (0.95 : ℝ) * (N : ℝ) ^ (0.05 : ℝ) := by
      rw [← rpow_add hNp]; norm_num
    have hp : 0 ≤ (N : ℝ) ^ (0.95 : ℝ) := by positivity
    nlinarith
  · have : (N : ℝ) = (N : ℝ) ^ ((2 / 3 : ℝ) + 0.3) * (N : ℝ) ^ (1 / 30 : ℝ) := by
      rw [← rpow_add hNp]; norm_num
    have hp : 0 ≤ (N : ℝ) ^ ((2 / 3 : ℝ) + 0.3) := by positivity
    nlinarith
  · have : (N : ℝ) = (N : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ) := by
      rw [← rpow_add hNp]; norm_num
    have hp : 0 ≤ (N : ℝ) ^ (2 / 3 : ℝ) := by positivity
    nlinarith
  · simp only [Real.norm_eq_abs] at hl
    have hL : 0 ≤ log (N : ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
    rw [abs_of_nonneg (rpow_nonneg hL _), abs_of_nonneg (by positivity)] at hl
    linarith

/-- The uniform Wu input of the lab, `WuUniformStmt`, follows from Wu 1993 Théorème 2,
display 1.7, in the form `WuTheorem2Stmt`, with θ = 0.95, ε = 0.2, λ = 1, C = 3.
PROVED from that hypothesis; no sorry. -/
theorem wuUniform_of_wuTheorem2 (hW : WuTheorem2Stmt) : WuUniformStmt := by
  intro A hA
  obtain ⟨B, hB, K, hK, x0, hx0⟩ :=
    hW 0.95 0.2 1 3 A (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA
  refine ⟨B, hB, K + 1, by linarith, ?_⟩
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp (wu2_eventually A B hB)
  refine ⟨max ⌈x0⌉₊ N1, fun N hN E hE => ?_⟩
  obtain ⟨hN3, hy3, h23, h4, hlog, hD1, hD2⟩ := hN1 N ((le_max_right ..).trans hN)
  have hx0N : x0 ≤ (N : ℝ) :=
    (Nat.le_ceil x0).trans (by exact_mod_cast (le_max_left ..).trans hN)
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  set y : ℝ := (N : ℝ) ^ (0.95 : ℝ) with hy
  set M : ℝ := (N : ℝ) - y with hMdef
  set T : ℝ := (N : ℝ) ^ (0.3 : ℝ) with hTdef
  set D : ℝ := sw2Level337 N B with hDdef
  set L : ℝ := log (N : ℝ) with hLdef
  have hy0 : 0 < y := by positivity
  have hyN : y < N := by linarith
  have hT1 : 1 ≤ T := one_le_rpow hN1r (by norm_num)
  have hTN : (N : ℝ) < T ^ 4 := by
    rw [hTdef, ← rpow_natCast, ← rpow_mul hNp.le]
    have h12 : (N : ℝ) ^ (1 : ℝ) < (N : ℝ) ^ ((0.3 : ℝ) * ((4 : ℕ) : ℝ)) :=
      rpow_lt_rpow_of_exponent_lt (by exact_mod_cast (show 1 < N by omega)) (by norm_num)
    simpa using h12
  have hM2 : (N : ℝ) / 2 < M := by rw [hMdef]; linarith
  have hlarge : ∀ e ∈ E, ∀ r : ℕ, M ≤ ((e * r : ℕ) : ℝ) → T ≤ r := by
    intro e he r hr
    by_contra hlt
    rw [not_le] at hlt
    have he2 := (hE e he).2
    have hprod : ((e * r : ℕ) : ℝ) < (N : ℝ) ^ ((2 / 3 : ℝ) + 0.3) := by
      rw [rpow_add hNp]; push_cast
      exact mul_lt_mul'' he2 hlt (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hN23 : (0 : ℝ) ≤ (N : ℝ) ^ ((2 / 3 : ℝ) + 0.3) := by positivity
    linarith
  have hE2 : ∀ e ∈ E, 2 ≤ M / e := by
    intro e he
    have hepos : (0 : ℝ) < e := by exact_mod_cast (hE e he).1
    rw [le_div_iff₀ hepos]
    have := (hE e he).2
    linarith
  -- Théorème 2 with g the indicator of E, a = N mod d, h = y, z = M.
  have hW' := hx0 N hx0N (fun l => if l ∈ E then 1 else 0)
    (wu_hyp14_of_abs_le_one _ (fun n => by split_ifs <;> norm_num))
    (fun d => if N.Coprime d then N % d else 1) (fun _ => y) (fun _ => M)
    (fun d => by
      split_ifs with hc
      · show Nat.gcd (N % d) d = 1
        rw [← Nat.gcd_rec]; exact hc.symm
      · exact Nat.coprime_one_left d)
    (fun _ => ⟨hy0.le, le_rfl⟩) (fun _ => ⟨hM2, by rw [hMdef]; linarith⟩)
  have e1 : ((0.95 : ℝ) - 1 / 2) = 0.45 := by norm_num
  have e2 : ((5 * (0.95 : ℝ) - 3) / 2 - 0.2) = 0.675 := by norm_num
  rw [e1, e2] at hW'
  -- On d coprime to N the Théorème 2 sum is the sum over E.
  have hS : ∀ d, N.Coprime d →
      (∑ l ∈ (Icc 1 ⌊(N : ℝ) ^ (0.675 : ℝ)⌋₊).filter (fun l => l.Coprime d),
        (if l ∈ E then (1 : ℝ) else 0) * wuH1 M y d (if N.Coprime d then N % d else 1) l) =
      ∑ e ∈ E.filter (fun e => e.Coprime d), wuH1 M y d (N % d) e := by
    intro d hd
    simp only [if_pos hd, ite_mul, one_mul, zero_mul]
    rw [← sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext a
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨_, hc⟩, ha⟩; exact ⟨ha, hc⟩
    · rintro ⟨ha, hc⟩
      refine ⟨⟨⟨(hE a ha).1, Nat.le_floor ?_⟩, hc⟩, ha⟩
      exact (hE a ha).2.le.trans (rpow_le_rpow_of_exponent_le hN1r (by norm_num))
  set Dc := (Icc 1 ⌊D⌋₊).filter (fun d => N.Coprime d)
  have hD0 : (0 : ℝ) ≤ D := le_trans (by positivity) hD1
  have hDfl1 : 1 ≤ ⌊D⌋₊ := Nat.le_floor (by
    push_cast; exact le_trans (one_le_rpow hN1r (by norm_num)) hD1)
  have herr : ∀ d ∈ Dc, swWu337 N d E ≤
      |∑ l ∈ (Icc 1 ⌊(N : ℝ) ^ (0.675 : ℝ)⌋₊).filter (fun l => l.Coprime d),
        (if l ∈ E then (1 : ℝ) else 0) * wuH1 M y d (if N.Coprime d then N % d else 1) l| +
        (3 + 3 * ((y / T) / d)) := by
    intro d hdm
    have hd : N.Coprime d := (mem_filter.mp hdm).2
    rw [hS d hd]
    refine (swWu_le_wuH1 N d E hyN hE2).trans ?_
    gcongr
    have h2 := sum_wuBadDvd1_le N d E hd (by omega) T hT1 hTN hlarge
    rw [← hy] at h2
    linarith
  have hharm : ∑ d ∈ Icc 1 ⌊D⌋₊, ((d : ℝ))⁻¹ ≤ 1 + log (⌊D⌋₊ : ℝ) := by
    have := harmonic_le_one_add_log ⌊D⌋₊
    rw [harmonic_eq_sum_Icc] at this
    push_cast at this
    exact this
  have hlogD : log (⌊D⌋₊ : ℝ) ≤ L := by
    apply log_le_log (by exact_mod_cast hDfl1)
    calc (⌊D⌋₊ : ℝ) ≤ D := Nat.floor_le hD0
      _ ≤ (N : ℝ) ^ (0.45 : ℝ) := hD2
      _ ≤ N := by
          calc (N : ℝ) ^ (0.45 : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) :=
                rpow_le_rpow_of_exponent_le hN1r (by norm_num)
            _ = N := rpow_one _
  have hL1 : 1 ≤ L := by
    rw [hLdef, ← log_exp 1]
    apply log_le_log (exp_pos 1)
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN3
    linarith [Real.exp_one_lt_d9]
  have hyT : y / T = (N : ℝ) ^ (0.65 : ℝ) := by
    rw [hy, hTdef, ← rpow_sub hNp]; norm_num
  have h45 : (N : ℝ) ^ (0.45 : ℝ) ≤ (N : ℝ) ^ (0.65 : ℝ) :=
    rpow_le_rpow_of_exponent_le hN1r (by norm_num)
  have h65 : 0 ≤ (N : ℝ) ^ (0.65 : ℝ) := by positivity
  have hErr : ∑ d ∈ Dc, (3 + 3 * ((y / T) / d)) ≤ y / L ^ A := by
    calc _ ≤ ∑ d ∈ Icc 1 ⌊D⌋₊, (3 + 3 * ((y / T) / d)) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
      _ = 3 * (⌊D⌋₊ : ℝ) + 3 * (y / T) * ∑ d ∈ Icc 1 ⌊D⌋₊, ((d : ℝ))⁻¹ := by
          rw [sum_add_distrib, sum_const, Nat.card_Icc, mul_sum]
          simp only [nsmul_eq_mul, Nat.add_sub_cancel]
          congr 1
          · ring
          · apply sum_congr rfl; intro d _; rw [div_eq_mul_inv]; ring
      _ ≤ 3 * (N : ℝ) ^ (0.65 : ℝ) + 3 * (N : ℝ) ^ (0.65 : ℝ) * (1 + L) := by
          rw [hyT]
          gcongr
          · exact (Nat.floor_le hD0).trans (hD2.trans h45)
          · exact hharm.trans (by linarith)
      _ ≤ 9 * (N : ℝ) ^ (0.65 : ℝ) * L := by nlinarith
      _ ≤ y / L ^ A := by
          have hLA : 0 < L ^ A := rpow_pos_of_pos (by linarith) _
          rw [le_div_iff₀ hLA]
          have hsplitL : L ^ (A + 1) = L ^ A * L := rpow_add_one (by linarith) A
          have hsplitN : y = (N : ℝ) ^ (0.65 : ℝ) * (N : ℝ) ^ (0.3 : ℝ) := by
            rw [hy, ← rpow_add hNp]; norm_num
          rw [hsplitN]
          calc 9 * (N : ℝ) ^ (0.65 : ℝ) * L * L ^ A
              = (N : ℝ) ^ (0.65 : ℝ) * (9 * L ^ (A + 1)) := by rw [hsplitL]; ring
            _ ≤ (N : ℝ) ^ (0.65 : ℝ) * (N : ℝ) ^ (0.3 : ℝ) := by gcongr
  have hWc : ∑ d ∈ Dc,
      |∑ l ∈ (Icc 1 ⌊(N : ℝ) ^ (0.675 : ℝ)⌋₊).filter (fun l => l.Coprime d),
        (if l ∈ E then (1 : ℝ) else 0) * wuH1 M y d (if N.Coprime d then N % d else 1) l| ≤
      K * y / L ^ A :=
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => abs_nonneg _)).trans hW'
  calc (∑ d ∈ Dc, swWu337 N d E)
      ≤ ∑ d ∈ Dc, (|∑ l ∈ (Icc 1 ⌊(N : ℝ) ^ (0.675 : ℝ)⌋₊).filter (fun l => l.Coprime d),
          (if l ∈ E then (1 : ℝ) else 0) * wuH1 M y d (if N.Coprime d then N % d else 1) l| +
          (3 + 3 * ((y / T) / d))) := sum_le_sum herr
    _ = _ + _ := sum_add_distrib
    _ ≤ K * y / L ^ A + y / L ^ A := add_le_add hWc hErr
    _ = (K + 1) * y / L ^ A := by ring

/-- P0044, the Theorem of pages 597 to 598, CONDITIONAL ON BJS Theorem 6 and on Wu 1993
Théorème 2, display 1.7, page 111, in the form `WuTheorem2Stmt`. -/
theorem cai2002_main_theorem_wu
    (h6 : LeanLab.ChenExplicit.Theorem6Stmt) (hW : WuTheorem2Stmt) : MainTheorem :=
  cai2002_main_theorem_conditional h6 (wuUniform_of_wuTheorem2 hW)

#print axioms wuUniform_of_wuTheorem2
#print axioms cai2002_main_theorem_wu

end LeanLab.Cai2002
