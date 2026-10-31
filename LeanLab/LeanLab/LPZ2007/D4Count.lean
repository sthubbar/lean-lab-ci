/-
P0045 Languasco, Pintz, Zaccagnini 2007, p.8, displays (18) to (20), the elementary count: for a
modulus `d` and a period `ξ ≥ 1` of `2` mod `d`, `2^ξ ≡ 1`, the number of `ν ∈ [1, M]^k` with
`2^{ν_1} + … + 2^{ν_k} ≡ t mod d` lies between `q^k` and `(q + 1)^k` times the number with
`ν ∈ [1, ξ]^k`, where `q = ⌊M/ξ⌋`. With `ξ = ξ(d)` and `t = N` the latter number is the paper's
`j(d, k, N)` of (18), so the count is `j(d, k, N) (L'/ξ(d))^k (1 + O(ξ(d)/L'))` for each fixed `d`.

Unit U-6835, CLOUD 20261021T0217Z-cloud56, track T2. AI-written Lean code, Claude. Checked only by
the Lean kernel. KNOWN mathematics. Binary Goldbach is OPEN.

* `sum_Icc_periodic`: a periodic sum over `[1, M]` is `q` to `q + 1` times one period.
* `cnt_succ`: the count for `k + 1` is a sum over the first exponent of counts for `k`.
* `cnt_bounds`: `q^k cnt(ξ) ≤ cnt(M) ≤ (q + 1)^k cnt(ξ)`.
* `jd_eq_cnt`: `j(d, k, N) = cnt(ξ(d))` at `t = N`.
-/
import Mathlib
import LeanLab.LPZ2007.Eq14FromCor42

namespace LeanLab.LPZ2007.D4Count

open Finset LeanLab.LPZ2007 LeanLab.LPZ2007.Eq14FromCor42

/-- `#{ν ∈ [1, M]^k : 2^{ν_1} + … + 2^{ν_k} ≡ t mod d}`. -/
def cnt (d k M : ℕ) (t : ZMod d) : ℕ :=
  ∑ ν ∈ tuples k M, if ((pow2sum ν : ℕ) : ZMod d) = t then 1 else 0

/-- One period repeated: `Σ_{a ∈ [1, qξ]} F a = q Σ_{b ∈ [1, ξ]} F b` for `F` of period `ξ`. -/
theorem sum_Icc_mul {F : ℕ → ℕ} {ξ : ℕ} (hF : ∀ a, F (a + ξ) = F a) (q : ℕ) :
    ∑ a ∈ Icc 1 (q * ξ), F a = q * ∑ b ∈ Icc 1 ξ, F b := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hsplit : Icc 1 ((q + 1) * ξ) = Icc 1 (q * ξ) ∪ Icc (q * ξ + 1) (q * ξ + ξ) := by
      ext a; simp only [mem_union, mem_Icc]; constructor
      · intro h; by_cases ha : a ≤ q * ξ
        · exact Or.inl ⟨h.1, ha⟩
        · right; constructor <;> nlinarith
      · rintro (h | h) <;> constructor <;> nlinarith
    have hdisj : Disjoint (Icc 1 (q * ξ)) (Icc (q * ξ + 1) (q * ξ + ξ)) := by
      rw [disjoint_left]; intro a h1 h2; simp only [mem_Icc] at h1 h2; omega
    have hshift : ∀ m : ℕ, ∑ a ∈ Icc (m * ξ + 1) (m * ξ + ξ), F a = ∑ b ∈ Icc 1 ξ, F b := by
      intro m
      induction m with
      | zero => simp
      | succ m ihm =>
        rw [← ihm]
        have : Icc ((m + 1) * ξ + 1) ((m + 1) * ξ + ξ) =
            (Icc (m * ξ + 1) (m * ξ + ξ)).map (addRightEmbedding ξ) := by
          rw [map_add_right_Icc]; congr 1 <;> ring
        rw [this, sum_map]
        exact sum_congr rfl fun a _ => hF a
    rw [hsplit, sum_union hdisj, ih, hshift q]; ring

/-- **A periodic sum over `[1, M]`** lies between `q` and `q + 1` periods, `q = ⌊M/ξ⌋`. -/
theorem sum_Icc_periodic {F : ℕ → ℕ} {ξ : ℕ} (hξ : 0 < ξ) (hF : ∀ a, F (a + ξ) = F a) (M : ℕ) :
    (M / ξ) * ∑ b ∈ Icc 1 ξ, F b ≤ ∑ a ∈ Icc 1 M, F a ∧
      ∑ a ∈ Icc 1 M, F a ≤ (M / ξ + 1) * ∑ b ∈ Icc 1 ξ, F b := by
  have h1 : M / ξ * ξ ≤ M := Nat.div_mul_le_self M ξ
  have h2 : M ≤ (M / ξ + 1) * ξ := by
    have := Nat.lt_div_mul_add hξ (a := M); nlinarith
  constructor
  · rw [← sum_Icc_mul hF]
    exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right h1) (fun _ _ _ => Nat.zero_le _)
  · rw [← sum_Icc_mul hF]
    exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right h2) (fun _ _ _ => Nat.zero_le _)

/-- The recursion over the first exponent. -/
theorem cnt_succ (d k M : ℕ) (t : ZMod d) :
    cnt d (k + 1) M t = ∑ a ∈ Icc 1 M, cnt d k M (t - 2 ^ a) := by
  unfold cnt
  rw [sum_tuples_succ, sum_comm]
  refine sum_congr rfl fun a _ => sum_congr rfl fun ν _ => ?_
  rw [pow2sum_cons]
  push_cast
  congr 1
  apply propext
  constructor <;> intro h <;> [rw [← h]; rw [h]] <;> ring

theorem cnt_zero' (d M : ℕ) (t : ZMod d) : cnt d 0 M t = if (0 : ZMod d) = t then 1 else 0 := by
  unfold cnt
  have h : tuples 0 M = {Fin.elim0} := by
    ext ν; simp only [tuples, Fintype.mem_piFinset, mem_singleton]
    constructor
    · intro _; funext i; exact i.elim0
    · intro _ i; exact i.elim0
  rw [h, sum_singleton]; simp [pow2sum]

theorem cnt_zero (d M : ℕ) (t : ZMod d) : cnt d 0 M t = cnt d 0 1 t := by
  rw [cnt_zero', cnt_zero']

/-- **The count for each fixed `d`**: `q^k cnt(ξ) ≤ cnt(M) ≤ (q + 1)^k cnt(ξ)`, `q = ⌊M/ξ⌋`. -/
theorem cnt_bounds {d ξ : ℕ} (hξ : 0 < ξ) (h2 : (2 : ZMod d) ^ ξ = 1) (M k : ℕ) (t : ZMod d) :
    (M / ξ) ^ k * cnt d k ξ t ≤ cnt d k M t ∧ cnt d k M t ≤ (M / ξ + 1) ^ k * cnt d k ξ t := by
  induction k generalizing t with
  | zero =>
    rw [cnt_zero d M, cnt_zero d ξ]; simp
  | succ k ih =>
    have hper : ∀ a, cnt d k ξ (t - 2 ^ (a + ξ)) = cnt d k ξ (t - 2 ^ a) := by
      intro a; rw [pow_add, h2, mul_one]
    obtain ⟨hlo, hhi⟩ := sum_Icc_periodic (F := fun a => cnt d k ξ (t - 2 ^ a)) hξ hper M
    simp only [cnt_succ]
    constructor
    · calc (M / ξ) ^ (k + 1) * ∑ a ∈ Icc 1 ξ, cnt d k ξ (t - 2 ^ a)
          = (M / ξ) ^ k * ((M / ξ) * ∑ a ∈ Icc 1 ξ, cnt d k ξ (t - 2 ^ a)) := by ring
        _ ≤ (M / ξ) ^ k * ∑ a ∈ Icc 1 M, cnt d k ξ (t - 2 ^ a) := Nat.mul_le_mul_left _ hlo
        _ = ∑ a ∈ Icc 1 M, (M / ξ) ^ k * cnt d k ξ (t - 2 ^ a) := by rw [mul_sum]
        _ ≤ ∑ a ∈ Icc 1 M, cnt d k M (t - 2 ^ a) := sum_le_sum fun a _ => (ih _).1
    · calc ∑ a ∈ Icc 1 M, cnt d k M (t - 2 ^ a)
          ≤ ∑ a ∈ Icc 1 M, (M / ξ + 1) ^ k * cnt d k ξ (t - 2 ^ a) :=
            sum_le_sum fun a _ => (ih _).2
        _ = (M / ξ + 1) ^ k * ∑ a ∈ Icc 1 M, cnt d k ξ (t - 2 ^ a) := by rw [mul_sum]
        _ ≤ (M / ξ + 1) ^ k * ((M / ξ + 1) * ∑ a ∈ Icc 1 ξ, cnt d k ξ (t - 2 ^ a)) :=
            Nat.mul_le_mul_left _ hhi
        _ = (M / ξ + 1) ^ (k + 1) * ∑ a ∈ Icc 1 ξ, cnt d k ξ (t - 2 ^ a) := by ring

/-- `ξ(d) = orderOf 2` is a period of `2` mod `d`, positive for odd `d`. -/
theorem xi_spec {d : ℕ} (hd : Odd d) : 0 < xi d ∧ (2 : ZMod d) ^ xi d = 1 := by
  have hcop : Nat.Coprime 2 d := (Nat.coprime_two_left).2 hd
  have hu : IsUnit (2 : ZMod d) := by
    have := (ZMod.unitOfCoprime 2 hcop).isUnit
    simpa using this
  unfold xi
  refine ⟨?_, pow_orderOf_eq_one _⟩
  rcases Nat.eq_zero_or_pos d with h0 | h0
  · subst h0; exact absurd hd (by decide)
  · have : NeZero d := ⟨h0.ne'⟩
    exact orderOf_pos_iff.2 (hu.isOfFinOrder)

/-- `j(d, k, N)` of (18) is the count with `ν ∈ [1, ξ(d)]^k`. -/
theorem jd_eq_cnt (d k N : ℕ) : jd d k N = cnt d k (xi d) (N : ZMod d) := by
  classical
  unfold jd cnt
  rw [card_filter]
  refine sum_congr rfl fun ν _ => ?_
  congr 1
  apply propext
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [sub_eq_zero, eq_comm]

/-- **(18) to (19) for each odd `d`**: with `q = ⌊M/ξ(d)⌋`,
`q^k j(d, k, N) ≤ #{ν ∈ [1, M]^k : 2^{ν_1} + … + 2^{ν_k} ≡ N mod d} ≤ (q + 1)^k j(d, k, N)`. -/
theorem count_jd_bounds {d : ℕ} (hd : Odd d) (M k N : ℕ) :
    (M / xi d) ^ k * jd d k N ≤ cnt d k M (N : ZMod d) ∧
      cnt d k M (N : ZMod d) ≤ (M / xi d + 1) ^ k * jd d k N := by
  rw [jd_eq_cnt]
  exact cnt_bounds (xi_spec hd).1 (xi_spec hd).2 M k _

/-- The count in `D4` is `cnt` at `t = N` once every `2^{ν_1} + … + 2^{ν_k} ≤ N`. -/
theorem D4count_eq_cnt (d k M N : ℕ) (h : ∀ ν ∈ tuples k M, pow2sum ν ≤ N) :
    #{ν ∈ tuples k M | d ∣ N - pow2sum ν} = cnt d k M (N : ZMod d) := by
  classical
  unfold cnt
  rw [card_filter]
  refine sum_congr rfl fun ν hν => ?_
  congr 1
  apply propext
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (h ν hν), sub_eq_zero, eq_comm]

/-- **The `d`-th count of (17), for odd `d`**: between `q^k j(d, k, N)` and `(q + 1)^k j(d, k, N)`,
`q = ⌊M/ξ(d)⌋`, `M = ⌊L'⌋`. -/
theorem D4count_bounds {d : ℕ} (hd : Odd d) (k : ℕ) (X : ℝ) (N : ℕ)
    (h : ∀ ν ∈ tuples k ⌊Lp X⌋₊, pow2sum ν ≤ N) :
    (⌊Lp X⌋₊ / xi d) ^ k * jd d k N ≤ #{ν ∈ tuples k ⌊Lp X⌋₊ | d ∣ N - pow2sum ν} ∧
      #{ν ∈ tuples k ⌊Lp X⌋₊ | d ∣ N - pow2sum ν} ≤ (⌊Lp X⌋₊ / xi d + 1) ^ k * jd d k N := by
  rw [D4count_eq_cnt d k _ N h]
  exact count_jd_bounds hd _ k N

end LeanLab.LPZ2007.D4Count
