/-
P0044, Cai 2002, Lemma 4 of page 599, quoted from J. Wu, Quart. J. Math. Oxford 44 (1993),
109 to 128, https://doi.org/10.1093/qmath/44.1.109.

`WuLemma4Stmt` states Lemma 4 as Cai prints it on page 599, specialised to θ = 0.95,
β = 2/3, x = N, for coefficients with |g| at most 1, so c = 1 with constant 1:
the closed left end z ≤ ap, every prime p, the max over l coprime to d, over h ≤ y and over
x/2 ≤ z ≤ x written as a bound for every choice of l, h and z at each d, and the sum over
all d ≤ D. The one reading beyond the printed text is that B, the implied constant and the
threshold do not depend on g inside this class; see the QUESTION in
research/burst-20261112/Cai2002-wu_lemma4-p2.md.

`wuUniform_of_lemma4` proves the lab's `WuUniformStmt`, the statement of the cited leaf
`leaf337_wu_uniform`, from `WuLemma4Stmt`. The two differences named in the wire2 note,
the strict left end of `switchedLocalCount337` and its coprimality of r to N, are bounded
here: each comes from at most three primes r above N^0.3, because four of them have product
above N. This proof is new Lean, not a step printed in Cai.

`cai2002_main_theorem_lemma4` is the Theorem of pages 597 to 598, CONDITIONAL ON BJS
Theorem 6 and on `WuLemma4Stmt`. No sorry is used in this file.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.Cai2002.MainConditional

open Filter Finset Real
open scoped Topology
noncomputable section
namespace LeanLab.Cai2002

/-- H(z, h, a, q, l) of Cai page 599, Lemma 4: the primes p with z ≤ ap < z + h and
ap ≡ l mod q, minus (Li((z+h)/a) - Li(z/a)) / φ(q). For a ≥ 1 every such p is below z + h,
so the finite range loses nothing. -/
def wuH (z h : ℝ) (a q l : ℕ) : ℝ :=
  ((((range ⌈z + h⌉₊).filter (fun p => p.Prime ∧ z ≤ ((a * p : ℕ) : ℝ) ∧
      ((a * p : ℕ) : ℝ) < z + h ∧ a * p ≡ l [MOD q])).card : ℕ) : ℝ) -
    1 / (q.totient : ℝ) * (li118 ((z + h) / a) - li118 (z / a))

/-- CITED STATEMENT, not proved. Cai page 599, Lemma 4, from Wu 1993, with θ = 0.95,
y = N^θ, β = 2/3 < (5θ - 3)/2, λ = θ - 1/2 and D = N^λ log^-B N, for every coefficient
sequence g with |g| ≤ 1, with B, K and N0 depending only on A. -/
def WuLemma4Stmt : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
    ∀ g : ℕ → ℝ, (∀ n, |g n| ≤ 1) →
    ∀ (l : ℕ → ℕ) (h z : ℕ → ℝ), (∀ d, (l d).Coprime d) →
      (∀ d, 0 ≤ h d ∧ h d ≤ (N : ℝ) ^ (0.95 : ℝ)) →
      (∀ d, (N : ℝ) / 2 ≤ z d ∧ z d ≤ N) →
      ∑ d ∈ Icc 1 ⌊sw2Level337 N B⌋₊,
        |∑ a ∈ (Icc 1 ⌊(N : ℝ) ^ (2 / 3 : ℝ)⌋₊).filter (fun a => a.Coprime d),
          g a * wuH (z d) (h d) a d (l d)| ≤ K * (N : ℝ) ^ (0.95 : ℝ) / log N ^ A

/-- At most three prime factors of m are at least T when T^4 > m. -/
theorem card_large_primeFactors_le (m : ℕ) (hm : m ≠ 0) (T : ℝ) (hT : 1 ≤ T)
    (hTm : (m : ℝ) < T ^ 4) :
    (m.primeFactors.filter (fun r : ℕ => T ≤ (r : ℝ))).card ≤ 3 := by
  by_contra hc
  rw [not_le] at hc
  set s := m.primeFactors.filter (fun r : ℕ => T ≤ (r : ℝ))
  have hdvd : ∏ r ∈ s, r ∣ m :=
    (Finset.prod_dvd_prod_of_subset _ _ id (filter_subset _ _)).trans (Nat.prod_primeFactors_dvd m)
  have hle : ∏ r ∈ s, r ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdvd
  have h1 : T ^ s.card ≤ ∏ r ∈ s, (r : ℝ) := by
    rw [← Finset.prod_const]
    gcongr with r hr
    exact (mem_filter.mp hr).2
  have h2 : T ^ 4 ≤ T ^ s.card := pow_le_pow_right₀ hT (by omega)
  have h3 : ((∏ r ∈ s, r : ℕ) : ℝ) ≤ m := by exact_mod_cast hle
  push_cast at h3
  linarith

/-- For r dividing N and d coprime to r, the e with N - y ≤ e r < N and d ∣ N - e r number
at most (y / r) / d, through k = N / r - e, a multiple of d in (0, y / r]. -/
theorem card_shift_dvd_le (r N d : ℕ) (hr : r ∣ N) (hd : d.Coprime r) (y : ℝ) (hy0 : 0 ≤ y)
    (hr0 : 0 < r) (S : Finset ℕ)
    (hS : ∀ e ∈ S, (N : ℝ) - y ≤ ((e * r : ℕ) : ℝ) ∧ e * r < N ∧ d ∣ N - e * r) :
    (S.card : ℝ) ≤ (y / r) / d := by
  obtain ⟨n, rfl⟩ := hr
  have hinj : Set.InjOn (fun e => n - e) S := by
    intro a ha b hb hab
    have := (hS a ha).2.1; have := (hS b hb).2.1
    have ha' : a < n := by
      by_contra h; rw [not_lt] at h; nlinarith [Nat.mul_le_mul_left r h]
    have hb' : b < n := by
      by_contra h; rw [not_lt] at h; nlinarith [Nat.mul_le_mul_left r h]
    simp only at hab; omega
  have hmap : ∀ e ∈ S, (fun e => n - e) e ∈ (Ioc 0 ⌊y / r⌋₊).filter (fun k => d ∣ k) := by
    intro e he
    obtain ⟨h1, h2, h3⟩ := hS e he
    have hen : e < n := by
      by_contra h; rw [not_lt] at h; nlinarith [Nat.mul_le_mul_left r h]
    simp only [mem_filter, mem_Ioc]
    have hsub : r * n - e * r = r * (n - e) := by
      rw [Nat.mul_sub, mul_comm e r]
    refine ⟨⟨by omega, ?_⟩, ?_⟩
    · apply Nat.le_floor
      rw [le_div_iff₀ (by exact_mod_cast hr0)]
      have hcast : ((r * (n - e) : ℕ) : ℝ) = ((r * n : ℕ) : ℝ) - ((e * r : ℕ) : ℝ) := by
        rw [← hsub, Nat.cast_sub (by nlinarith)]
      have : ((n - e : ℕ) : ℝ) * r = ((r * (n - e) : ℕ) : ℝ) := by push_cast; ring
      rw [this, hcast]; linarith
    · rw [hsub] at h3
      exact hd.dvd_of_dvd_mul_left h3
  have hc := Finset.card_le_card_of_injOn _ hmap hinj
  rw [Nat.Ioc_filter_dvd_card_eq_div] at hc
  calc (S.card : ℝ) ≤ ((⌊y / r⌋₊ / d : ℕ) : ℝ) := by exact_mod_cast hc
    _ ≤ (⌊y / r⌋₊ : ℝ) / d := Nat.cast_div_le
    _ ≤ (y / r) / d :=
        div_le_div_of_nonneg_right (Nat.floor_le (div_nonneg hy0 (Nat.cast_nonneg _)))
          (Nat.cast_nonneg _)

/-- The primes r with e r exactly at the left end N - N^0.95, which Lemma 4 counts and the
strict count `switchedLocalCount337` does not. -/
def wuBadEnd (N d e : ℕ) : Finset ℕ :=
  (range N).filter (fun r => r.Prime ∧
    ((e * r : ℕ) : ℝ) = (N : ℝ) - (N : ℝ) ^ (0.95 : ℝ) ∧ d ∣ N - e * r)

/-- The primes r dividing N, which Lemma 4 counts and `switchedLocalCount337` does not. -/
def wuBadDvd (N d e : ℕ) : Finset ℕ :=
  (range N).filter (fun r => r.Prime ∧ r ∣ N ∧
    (N : ℝ) - (N : ℝ) ^ (0.95 : ℝ) ≤ ((e * r : ℕ) : ℝ) ∧ e * r < N ∧ d ∣ N - e * r)

/-- The prime count of H at z = N - N^0.95, h = N^0.95, a = e, l = N mod d. -/
def wuCount (N d e : ℕ) : Finset ℕ :=
  (range N).filter (fun p => p.Prime ∧ (N : ℝ) - (N : ℝ) ^ (0.95 : ℝ) ≤ ((e * p : ℕ) : ℝ) ∧
    ((e * p : ℕ) : ℝ) < N ∧ e * p ≡ N % d [MOD d])

theorem wuH_switched (N d e : ℕ) :
    wuH ((N : ℝ) - (N : ℝ) ^ (0.95 : ℝ)) ((N : ℝ) ^ (0.95 : ℝ)) e d (N % d) =
      ((wuCount N d e).card : ℝ) - switchedLiTerm337 N e / d.totient := by
  unfold wuH wuCount switchedLiTerm337
  rw [sub_add_cancel, Nat.ceil_natCast]
  ring

theorem modEq_mod_iff_dvd (N d m : ℕ) (hm : m ≤ N) : m ≡ N % d [MOD d] ↔ d ∣ N - m := by
  rw [← Nat.modEq_iff_dvd' hm]
  exact ⟨fun h => h.trans (Nat.mod_modEq N d), fun h => h.trans (Nat.mod_modEq N d).symm⟩

/-- The strict count is at most the count of Lemma 4, which exceeds it by at most the two
bad sets. -/
theorem wuCount_bounds (N d e : ℕ) :
    switchedLocalCount337 N e d ≤ (wuCount N d e).card ∧
      (wuCount N d e).card ≤
        switchedLocalCount337 N e d + (wuBadEnd N d e).card + (wuBadDvd N d e).card := by
  unfold switchedLocalCount337
  constructor
  · apply card_le_card
    intro r hr
    simp only [wuCount, mem_filter] at hr ⊢
    obtain ⟨hrN, hp, _, h1, h2, h3⟩ := hr
    exact ⟨hrN, hp, h1.le, by exact_mod_cast h2, (modEq_mod_iff_dvd N d _ h2.le).2 h3⟩
  · have hsub : wuCount N d e ⊆ ((range N).filter (fun r => r.Prime ∧ r.Coprime N ∧
        (N : ℝ) - (N : ℝ) ^ (0.95 : ℝ) < (e * r : ℕ) ∧ e * r < N ∧ d ∣ N - e * r)) ∪
        wuBadEnd N d e ∪ wuBadDvd N d e := by
      intro p hp
      simp only [wuCount, mem_filter] at hp
      obtain ⟨hpN, hpp, h1, h2, h3⟩ := hp
      have hlt : e * p < N := by exact_mod_cast h2
      have hdv := (modEq_mod_iff_dvd N d _ hlt.le).1 h3
      simp only [mem_union, wuBadEnd, wuBadDvd, mem_filter]
      by_cases hc : p.Coprime N
      · by_cases heq : ((e * p : ℕ) : ℝ) = (N : ℝ) - (N : ℝ) ^ (0.95 : ℝ)
        · exact Or.inl (Or.inr ⟨hpN, hpp, heq, hdv⟩)
        · exact Or.inl (Or.inl ⟨hpN, hpp, hc, lt_of_le_of_ne h1 (Ne.symm heq), hlt, hdv⟩)
      · have : p ∣ N := by
          by_contra hn; exact hc ((Nat.Prime.coprime_iff_not_dvd hpp).2 hn)
        exact Or.inr ⟨hpN, hpp, this, h1, hlt, hdv⟩
    calc (wuCount N d e).card ≤ _ := card_le_card hsub
      _ ≤ _ := card_union_le _ _
      _ ≤ _ := by gcongr; exact card_union_le _ _

/-- One modulus: the lab remainder is at most the Lemma 4 sum plus the two bad counts. -/
theorem swWu_le_wuH (N d : ℕ) (E : Finset ℕ) :
    swWu337 N d E ≤
      |∑ e ∈ E.filter (fun e => e.Coprime d),
          wuH ((N : ℝ) - (N : ℝ) ^ (0.95 : ℝ)) ((N : ℝ) ^ (0.95 : ℝ)) e d (N % d)| +
        ∑ e ∈ E, (((wuBadEnd N d e).card : ℝ) + (wuBadDvd N d e).card) := by
  unfold swWu337
  set E' := E.filter (fun e => e.Coprime d)
  have hsplit : (∑ e ∈ E', ((switchedLocalCount337 N e d : ℝ) -
        switchedLiTerm337 N e / d.totient)) =
      (∑ e ∈ E', wuH ((N : ℝ) - (N : ℝ) ^ (0.95 : ℝ)) ((N : ℝ) ^ (0.95 : ℝ)) e d (N % d)) -
        ∑ e ∈ E', (((wuCount N d e).card : ℝ) - switchedLocalCount337 N e d) := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro e _
    rw [wuH_switched]
    ring
  have hnn : 0 ≤ ∑ e ∈ E', (((wuCount N d e).card : ℝ) - switchedLocalCount337 N e d) := by
    apply sum_nonneg
    intro e _
    have := (wuCount_bounds N d e).1
    have : (switchedLocalCount337 N e d : ℝ) ≤ (wuCount N d e).card := by exact_mod_cast this
    linarith
  rw [hsplit]
  refine (abs_sub _ _).trans ?_
  rw [abs_of_nonneg hnn]
  gcongr
  calc _ ≤ ∑ e ∈ E', (((wuBadEnd N d e).card : ℝ) + (wuBadDvd N d e).card) := by
        apply sum_le_sum
        intro e _
        have := (wuCount_bounds N d e).2
        have : ((wuCount N d e).card : ℝ) ≤ (switchedLocalCount337 N e d : ℝ) +
            (wuBadEnd N d e).card + (wuBadDvd N d e).card := by exact_mod_cast this
        linarith
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)

/-- The pairs at the exact left end: at most three over all e in E. -/
theorem sum_wuBadEnd_le (N d : ℕ) (E : Finset ℕ) (T : ℝ) (hT : 1 ≤ T)
    (hTN : (N : ℝ) < T ^ 4) (hM : 1 ≤ (N : ℝ) - (N : ℝ) ^ (0.95 : ℝ))
    (hlarge : ∀ e ∈ E, ∀ r : ℕ,
      (N : ℝ) - (N : ℝ) ^ (0.95 : ℝ) ≤ ((e * r : ℕ) : ℝ) → T ≤ r) :
    ∑ e ∈ E, (wuBadEnd N d e).card ≤ 3 := by
  set K0 := ⌊(N : ℝ) - (N : ℝ) ^ (0.95 : ℝ)⌋₊
  have hK0 : K0 ≠ 0 := by
    have : 1 ≤ K0 := Nat.le_floor (by exact_mod_cast hM)
    omega
  have hK0N : (K0 : ℝ) < T ^ 4 := by
    have hfl : (K0 : ℝ) ≤ (N : ℝ) - (N : ℝ) ^ (0.95 : ℝ) := Nat.floor_le (by linarith)
    have : (N : ℝ) ^ (0.95 : ℝ) ≥ 0 := by positivity
    linarith
  set R := K0.primeFactors.filter (fun r : ℕ => T ≤ (r : ℝ))
  have hswap : ∑ e ∈ E, (wuBadEnd N d e).card =
      ∑ r ∈ range N, (E.filter (fun e => r.Prime ∧
        ((e * r : ℕ) : ℝ) = (N : ℝ) - (N : ℝ) ^ (0.95 : ℝ) ∧ d ∣ N - e * r)).card := by
    simp only [wuBadEnd, card_filter]
    exact sum_comm
  rw [hswap]
  calc _ ≤ ∑ r ∈ range N, (if r ∈ R then 1 else 0) := by
        apply sum_le_sum
        intro r _
        split_ifs with hr
        · apply card_le_one.mpr
          intro a ha b hb
          simp only [mem_filter] at ha hb
          have hab : ((a * r : ℕ) : ℝ) = ((b * r : ℕ) : ℝ) := by rw [ha.2.2.1, hb.2.2.1]
          have hab' : a * r = b * r := by exact_mod_cast hab
          exact Nat.eq_of_mul_eq_mul_right ha.2.1.pos hab'
        · apply le_of_eq
          rw [card_eq_zero, filter_eq_empty_iff]
          rintro e he ⟨hp, heq, _⟩
          apply hr
          have hK : K0 = e * r := by
            simp only [K0]; rw [← heq, Nat.floor_natCast]
          simp only [R, mem_filter, Nat.mem_primeFactors]
          exact ⟨⟨hp, ⟨e, by rw [hK, mul_comm]⟩, hK0⟩, hlarge e he r heq.ge⟩
    _ = ((range N).filter (· ∈ R)).card := by rw [card_filter]
    _ ≤ R.card := card_le_card (fun r hr => (mem_filter.mp hr).2)
    _ ≤ 3 := card_large_primeFactors_le K0 hK0 T hT hK0N

/-- The pairs with r dividing N: at most 3 (y / T) / d over all e in E, for d coprime to N. -/
theorem sum_wuBadDvd_le (N d : ℕ) (E : Finset ℕ) (hd : N.Coprime d) (hN : N ≠ 0)
    (T : ℝ) (hT : 1 ≤ T) (hTN : (N : ℝ) < T ^ 4)
    (hlarge : ∀ e ∈ E, ∀ r : ℕ,
      (N : ℝ) - (N : ℝ) ^ (0.95 : ℝ) ≤ ((e * r : ℕ) : ℝ) → T ≤ r) :
    ∑ e ∈ E, ((wuBadDvd N d e).card : ℝ) ≤ 3 * (((N : ℝ) ^ (0.95 : ℝ) / T) / d) := by
  have hy0 : (0 : ℝ) ≤ (N : ℝ) ^ (0.95 : ℝ) := by positivity
  set c := ((N : ℝ) ^ (0.95 : ℝ) / T) / d
  have hc0 : 0 ≤ c := by positivity
  set R := N.primeFactors.filter (fun r : ℕ => T ≤ (r : ℝ))
  have hswap : ∑ e ∈ E, ((wuBadDvd N d e).card : ℝ) =
      ∑ r ∈ range N, ((E.filter (fun e => r.Prime ∧ r ∣ N ∧
        (N : ℝ) - (N : ℝ) ^ (0.95 : ℝ) ≤ ((e * r : ℕ) : ℝ) ∧ e * r < N ∧
          d ∣ N - e * r)).card : ℝ) := by
    simp only [wuBadDvd, card_filter]
    push_cast
    exact sum_comm
  rw [hswap]
  calc _ ≤ ∑ r ∈ range N, (if r ∈ R then c else 0) := by
        apply sum_le_sum
        intro r _
        split_ifs with hr
        · simp only [R, mem_filter, Nat.mem_primeFactors] at hr
          obtain ⟨⟨hp, hrN, _⟩, hTr⟩ := hr
          have hdr : d.Coprime r := (Nat.Coprime.coprime_dvd_left hrN hd).symm
          refine (card_shift_dvd_le r N d hrN hdr _ hy0 hp.pos _ ?_).trans ?_
          · intro e he
            simp only [mem_filter] at he
            exact ⟨he.2.2.2.1, he.2.2.2.2.1, he.2.2.2.2.2⟩
          · have hT0 : 0 < T := by linarith
            apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
            exact div_le_div_of_nonneg_left hy0 hT0 hTr
        · apply le_of_eq
          norm_cast
          rw [card_eq_zero, filter_eq_empty_iff]
          rintro e he ⟨hp, hrN, hle, _⟩
          apply hr
          simp only [R, mem_filter, Nat.mem_primeFactors]
          exact ⟨⟨hp, hrN, hN⟩, hlarge e he r hle⟩
    _ = ((range N).filter (· ∈ R)).card * c := by
        rw [← sum_filter, sum_const, nsmul_eq_mul]
    _ ≤ 3 * c := by
        gcongr
        have h1 : ((range N).filter (· ∈ R)).card ≤ R.card :=
          card_le_card (fun r hr => (mem_filter.mp hr).2)
        have h2 := card_large_primeFactors_le N hN T hT hTN
        exact_mod_cast h1.trans h2

/-- The large N facts used below. -/
theorem wu_eventually (A B : ℝ) (hB : 0 < B) :
    ∀ᶠ N : ℕ in atTop, 3 ≤ N ∧ 2 * (N : ℝ) ^ (0.95 : ℝ) ≤ N ∧
      2 * (N : ℝ) ^ ((2 / 3 : ℝ) + 0.3) ≤ N ∧
      9 * log N ^ (A + 1) ≤ (N : ℝ) ^ (0.3 : ℝ) ∧
      (N : ℝ) ^ (0.25 : ℝ) ≤ sw2Level337 N B ∧ sw2Level337 N B ≤ (N : ℝ) ^ (0.45 : ℝ) := by
  have hpow (a : ℝ) (ha : 0 < a) : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ a :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop |>.eventually
      (eventually_ge_atTop 2)
  have hlo := (isLittleO_log_rpow_rpow_atTop (A + 1) (by norm_num : (0 : ℝ) < 0.3)).bound
    (by norm_num : (0 : ℝ) < 1 / 9)
  have hlo' := tendsto_natCast_atTop_atTop.eventually hlo
  filter_upwards [eventually_ge_atTop 3, hpow 0.05 (by norm_num), hpow (1 / 30) (by norm_num),
    hlo', sw2_level_bounds337 B hB] with N hN3 h05 h30 hl hlev
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  refine ⟨hN3, ?_, ?_, ?_, hlev⟩
  · have : (N : ℝ) = (N : ℝ) ^ (0.95 : ℝ) * (N : ℝ) ^ (0.05 : ℝ) := by
      rw [← rpow_add hNp]; norm_num
    have hp : 0 ≤ (N : ℝ) ^ (0.95 : ℝ) := by positivity
    nlinarith
  · have : (N : ℝ) = (N : ℝ) ^ ((2 / 3 : ℝ) + 0.3) * (N : ℝ) ^ (1 / 30 : ℝ) := by
      rw [← rpow_add hNp]; norm_num
    have hp : 0 ≤ (N : ℝ) ^ ((2 / 3 : ℝ) + 0.3) := by positivity
    nlinarith
  · simp only [Real.norm_eq_abs] at hl
    have hL : 0 ≤ log (N : ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
    rw [abs_of_nonneg (rpow_nonneg hL _), abs_of_nonneg (by positivity)] at hl
    linarith

/-- The uniform Wu input of the lab, `WuUniformStmt`, follows from Lemma 4 as Cai prints
it, `WuLemma4Stmt`. PROVED from that hypothesis; no sorry. -/
theorem wuUniform_of_lemma4 (hW : WuLemma4Stmt) : WuUniformStmt := by
  intro A hA
  obtain ⟨B, hB, K, hK, N0, hN0⟩ := hW A hA
  refine ⟨B, hB, K + 1, by linarith, ?_⟩
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp (wu_eventually A B hB)
  refine ⟨max N0 N1, fun N hN E hE => ?_⟩
  obtain ⟨hN3, hy2, h23, hlog, hD1, hD2⟩ := hN1 N ((le_max_right ..).trans hN)
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  set y : ℝ := (N : ℝ) ^ (0.95 : ℝ) with hy
  set M : ℝ := (N : ℝ) - y with hMdef
  set T : ℝ := (N : ℝ) ^ (0.3 : ℝ) with hTdef
  set D : ℝ := sw2Level337 N B with hDdef
  set L : ℝ := log (N : ℝ) with hLdef
  have hy0 : 0 < y := by positivity
  have hT1 : 1 ≤ T := one_le_rpow hN1r (by norm_num)
  have hTN : (N : ℝ) < T ^ 4 := by
    rw [hTdef, ← rpow_natCast, ← rpow_mul hNp.le]
    have h12 : (N : ℝ) ^ (1 : ℝ) < (N : ℝ) ^ ((0.3 : ℝ) * ((4 : ℕ) : ℝ)) :=
      rpow_lt_rpow_of_exponent_lt (by exact_mod_cast (show 1 < N by omega)) (by norm_num)
    simpa using h12
  have hM2 : (N : ℝ) / 2 ≤ M := by rw [hMdef]; linarith
  have hM1 : 1 ≤ M := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN3
    linarith
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
  -- Lemma 4 with g the indicator of E, l = N mod d, h = y, z = M.
  have hW' := hN0 N ((le_max_left ..).trans hN) (fun a => if a ∈ E then 1 else 0)
    (fun n => by split_ifs <;> norm_num)
    (fun d => if N.Coprime d then N % d else 1) (fun _ => y) (fun _ => M)
    (fun d => by
      split_ifs with hc
      · show Nat.gcd (N % d) d = 1
        rw [← Nat.gcd_rec]; exact hc.symm
      · exact Nat.coprime_one_left d)
    (fun _ => ⟨hy0.le, le_rfl⟩) (fun _ => ⟨hM2, by rw [hMdef]; linarith⟩)
  -- On d coprime to N the Lemma 4 sum is the sum over E.
  have hS : ∀ d, N.Coprime d →
      (∑ a ∈ (Icc 1 ⌊(N : ℝ) ^ (2 / 3 : ℝ)⌋₊).filter (fun a => a.Coprime d),
        (if a ∈ E then (1 : ℝ) else 0) * wuH M y a d (if N.Coprime d then N % d else 1)) =
      ∑ e ∈ E.filter (fun e => e.Coprime d), wuH M y e d (N % d) := by
    intro d hd
    simp only [if_pos hd, ite_mul, one_mul, zero_mul]
    rw [← sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext a
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨_, hc⟩, ha⟩; exact ⟨ha, hc⟩
    · rintro ⟨ha, hc⟩
      exact ⟨⟨⟨(hE a ha).1, Nat.le_floor (hE a ha).2.le⟩, hc⟩, ha⟩
  set Dc := (Icc 1 ⌊D⌋₊).filter (fun d => N.Coprime d)
  have hD0 : (0 : ℝ) ≤ D := le_trans (by positivity) hD1
  have hDfl1 : 1 ≤ ⌊D⌋₊ := Nat.le_floor (by
    push_cast; exact le_trans (one_le_rpow hN1r (by norm_num)) hD1)
  -- error per modulus
  have herr : ∀ d ∈ Dc, swWu337 N d E ≤
      |∑ a ∈ (Icc 1 ⌊(N : ℝ) ^ (2 / 3 : ℝ)⌋₊).filter (fun a => a.Coprime d),
        (if a ∈ E then (1 : ℝ) else 0) * wuH M y a d (if N.Coprime d then N % d else 1)| +
        (3 + 3 * ((y / T) / d)) := by
    intro d hdm
    have hd : N.Coprime d := (mem_filter.mp hdm).2
    rw [hS d hd]
    refine (swWu_le_wuH N d E).trans ?_
    gcongr
    rw [sum_add_distrib]
    have h1 := sum_wuBadEnd_le N d E T hT1 hTN hM1 hlarge
    have h1' : ∑ e ∈ E, ((wuBadEnd N d e).card : ℝ) ≤ 3 := by exact_mod_cast h1
    have h2 := sum_wuBadDvd_le N d E hd (by omega) T hT1 hTN hlarge
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
  -- total error
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
  -- assemble
  have hWc : ∑ d ∈ Dc,
      |∑ a ∈ (Icc 1 ⌊(N : ℝ) ^ (2 / 3 : ℝ)⌋₊).filter (fun a => a.Coprime d),
        (if a ∈ E then (1 : ℝ) else 0) * wuH M y a d (if N.Coprime d then N % d else 1)| ≤
      K * y / L ^ A :=
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => abs_nonneg _)).trans hW'
  calc (∑ d ∈ Dc, swWu337 N d E)
      ≤ ∑ d ∈ Dc, (|∑ a ∈ (Icc 1 ⌊(N : ℝ) ^ (2 / 3 : ℝ)⌋₊).filter (fun a => a.Coprime d),
          (if a ∈ E then (1 : ℝ) else 0) * wuH M y a d (if N.Coprime d then N % d else 1)| +
          (3 + 3 * ((y / T) / d))) := sum_le_sum herr
    _ = _ + _ := sum_add_distrib
    _ ≤ K * y / L ^ A + y / L ^ A := add_le_add hWc hErr
    _ = (K + 1) * y / L ^ A := by ring

/-- P0044, the Theorem of pages 597 to 598, CONDITIONAL ON BJS Theorem 6 and on Lemma 4 of
page 599 as printed, in the form `WuLemma4Stmt`. -/
theorem cai2002_main_theorem_lemma4
    (h6 : LeanLab.ChenExplicit.Theorem6Stmt) (hW : WuLemma4Stmt) : MainTheorem :=
  cai2002_main_theorem_conditional h6 (wuUniform_of_lemma4 hW)

#print axioms wuUniform_of_lemma4
#print axioms cai2002_main_theorem_lemma4

end LeanLab.Cai2002
