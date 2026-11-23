/-
AI wrote this Lean code, Claude, ROUTE BURST S70, burst-20261122, unit buthe_compute_mid.
P0021 journal Lemma 5 first estimate p. 1216, cited there as Buthe 2014 display 4.6:
Q(z) ≤ 6 z / pi^2 + 0.68 sqrt z for z at least 1, Q the squarefree count.
Buthe's own proof is Cohen, Dress, El Marraki 2007 Theorem 3 plus "a short computer
calculation". This file holds the machinery for that calculation on the middle range,
done by the Legendre recursion for the count of integers free of the squares of a list
of primes, checked by the kernel at about 1100 checkpoints in the chunk files
Lemma5MuMidS70C*.lean.
No new definitions enter any statement of the paper; `phi`, `good` and `chkC` are
computational devices whose meaning is proved here.
Binary Goldbach is open.
-/
import Mathlib

namespace LeanLab.BS2022GRH.Lemma5MuMidS70
open Finset

/-- The squarefree count Q(N) of Buthe 2014 display 4.6, over `[1, N]`. -/
def S (N : ℕ) : ℕ := ((Icc 1 N).filter (fun m => Squarefree m)).card

/-- Integers in `[1, N]` free of `q * q` for every `q` in the list. -/
def A (L : List ℕ) (N : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun n => ∀ q ∈ L, ¬ q * q ∣ n)

/-- Legendre recursion for `card (A L N)`, valid for an increasing list of pairwise
coprime entries at least 2. -/
def phi : List ℕ → ℕ → ℕ
  | [], N => N
  | p :: ps, N => if N < p * p then N else phi ps N - phi ps (N / (p * p))

/-- The integer form of `Q ≤ 0.6079 m + 0.68 sqrt m`, as in Lemma5MuS63. -/
def good (m q : ℕ) : Bool :=
  decide (10000 * q ≤ 6079 * m) || decide ((10000 * q - 6079 * m) ^ 2 ≤ 46240000 * m)

/-- Consecutive checkpoint test: `good a (phi L b)` for consecutive checkpoints `a, b`. -/
def chkC (L : List ℕ) : List ℕ → Bool
  | a :: b :: rest => good a (phi L b) && chkC L (b :: rest)
  | _ => true

theorem A_nil (N : ℕ) : A [] N = Icc 1 N := by
  unfold A; ext n; simp

theorem A_card_le (L : List ℕ) (N : ℕ) : (A L N).card ≤ N := by
  unfold A
  calc _ ≤ (Icc 1 N).card := card_filter_le _ _
    _ = N := by simp

/-- Early exit: when `N < p * p` and every entry is at least `p`, nothing is removed. -/
theorem A_of_lt (p : ℕ) (ps : List ℕ) (N : ℕ) (hN : N < p * p) (hge : ∀ q ∈ ps, p ≤ q) :
    A (p :: ps) N = Icc 1 N := by
  unfold A
  ext n
  simp only [mem_filter, mem_Icc]
  constructor
  · intro h; exact h.1
  · intro h
    refine ⟨h, ?_⟩
    intro q hq hd
    have hqp : p ≤ q := by
      rcases List.mem_cons.1 hq with h' | h'
      · omega
      · exact hge q h'
    have h1 : 0 < n := by omega
    have h2 := Nat.le_of_dvd h1 hd
    have : p * p ≤ q * q := Nat.mul_le_mul hqp hqp
    omega

/-- Splitting step of the Legendre recursion. -/
theorem A_cons_card (p : ℕ) (ps : List ℕ) (N : ℕ) (hp : 2 ≤ p)
    (hcop : ∀ q ∈ ps, Nat.Coprime p q) :
    (A (p :: ps) N).card + (A ps (N / (p * p))).card = (A ps N).card := by
  have hpp : 0 < p * p := by positivity
  -- the part of `A ps N` divisible by `p * p`
  set B := (A ps N).filter (fun n => p * p ∣ n) with hB
  have hsplit : A (p :: ps) N = (A ps N).filter (fun n => ¬ p * p ∣ n) := by
    unfold A; ext n; simp only [mem_filter, List.mem_cons, forall_eq_or_imp]; tauto
  have himg : B = (A ps (N / (p * p))).map ⟨fun m => m * (p * p), mul_left_injective₀ hpp.ne'⟩ := by
    ext n
    simp only [hB, A, mem_filter, mem_map, mem_Icc]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      obtain ⟨m, rfl⟩ := h4
      refine ⟨m, ⟨⟨?_, ?_⟩, ?_⟩, by simp [mul_comm]⟩
      · rcases Nat.eq_zero_or_pos m with h | h
        · subst h; simp at h1
        · exact h
      · rw [Nat.le_div_iff_mul_le hpp]; linarith
      · intro q hq hd
        exact h3 q hq (Dvd.dvd.mul_left hd _)
    · rintro ⟨m, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, dvd_mul_left _ _⟩
      · exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
      · exact (Nat.le_div_iff_mul_le hpp).1 h2
      · intro q hq hd
        have hqp : Nat.Coprime q p := (hcop q hq).symm
        have hqq : Nat.Coprime (q * q) p := Nat.coprime_mul_iff_left.2 ⟨hqp, hqp⟩
        have hc : Nat.Coprime (q * q) (p * p) := Nat.coprime_mul_iff_right.2 ⟨hqq, hqq⟩
        exact h3 q hq (hc.dvd_of_dvd_mul_right hd)
  have hcard : B.card = (A ps (N / (p * p))).card := by rw [himg, card_map]
  rw [hsplit, ← hcard, hB, add_comm]
  exact card_filter_add_card_filter_not _

/-- Correctness of `phi`. -/
theorem phi_eq : ∀ (L : List ℕ) (N : ℕ), (∀ q ∈ L, 2 ≤ q) → L.Pairwise (· < ·) →
    L.Pairwise Nat.Coprime → phi L N = (A L N).card
  | [], N, _, _, _ => by simp [phi, A_nil]
  | p :: ps, N, h2, hs, hc => by
    have h2' : ∀ q ∈ ps, 2 ≤ q := fun q hq => h2 q (List.mem_cons_of_mem _ hq)
    have hs' := (List.pairwise_cons.1 hs).2
    have hc' := (List.pairwise_cons.1 hc).2
    unfold phi
    split_ifs with hN
    · rw [A_of_lt p ps N hN (fun q hq => le_of_lt ((List.pairwise_cons.1 hs).1 q hq))]
      simp
    · rw [phi_eq ps N h2' hs' hc', phi_eq ps (N / (p * p)) h2' hs' hc']
      have := A_cons_card p ps N (h2 p (by simp)) (List.pairwise_cons.1 hc).1
      omega

/-- Squarefree numbers avoid every square of an entry at least 2. -/
theorem S_le_A (L : List ℕ) (N : ℕ) (h2 : ∀ q ∈ L, 2 ≤ q) : S N ≤ (A L N).card := by
  unfold S A
  apply card_le_card
  intro n hn
  simp only [mem_filter] at hn ⊢
  refine ⟨hn.1, fun q hq hd => ?_⟩
  have hu := hn.2 q hd
  rw [Nat.isUnit_iff] at hu
  have := h2 q hq
  have : 4 ≤ q * q := Nat.mul_le_mul this this
  omega

theorem S_mono {a b : ℕ} (h : a ≤ b) : S a ≤ S b := by
  unfold S
  apply card_le_card
  intro n hn
  simp only [mem_filter, mem_Icc] at hn ⊢
  exact ⟨⟨hn.1.1, le_trans hn.1.2 h⟩, hn.2⟩

theorem real_of_good (N q : ℕ) (h : good N q = true) :
    (q : ℝ) ≤ 0.6079 * N + 0.68 * √(N : ℝ) := by
  simp only [good, Bool.or_eq_true, decide_eq_true_eq] at h
  have hs : 0 ≤ √(N : ℝ) := Real.sqrt_nonneg _
  rcases h with h | h
  · have : (10000 : ℝ) * q ≤ 6079 * N := by exact_mod_cast h
    nlinarith
  · by_cases hc : 10000 * q ≤ 6079 * N
    · have : (10000 : ℝ) * q ≤ 6079 * N := by exact_mod_cast hc
      nlinarith
    · have hc' : 6079 * N ≤ 10000 * q := by omega
      have hr : ((10000 * q - 6079 * N : ℕ) : ℝ) = 10000 * (q : ℝ) - 6079 * N := by
        push_cast [Nat.cast_sub hc']; ring
      have hsq : ((10000 : ℝ) * q - 6079 * N) ^ 2 ≤ 46240000 * N := by
        rw [← hr]; exact_mod_cast h
      have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
      have hss : √(N : ℝ) ^ 2 = N := Real.sq_sqrt hN
      have : (10000 : ℝ) * q - 6079 * N ≤ 6800 * √(N : ℝ) := by
        apply abs_le_of_sq_le_sq' _ (by positivity) |>.2
        nlinarith
      nlinarith

/-- The bound transported from a checkpoint `a` to any `N` with `a ≤ N ≤ b`. -/
theorem bound_between (L : List ℕ) (h2 : ∀ q ∈ L, 2 ≤ q) (hs : L.Pairwise (· < ·))
    (hc : L.Pairwise Nat.Coprime) (a b N : ℕ) (hg : good a (phi L b) = true)
    (haN : a ≤ N) (hNb : N ≤ b) :
    (S N : ℝ) ≤ 0.6079 * N + 0.68 * √(N : ℝ) := by
  have h1 : S N ≤ phi L b := by
    rw [phi_eq L b h2 hs hc]; exact le_trans (S_mono hNb) (S_le_A L b h2)
  have h3 := real_of_good a _ hg
  have h4 : (a : ℝ) ≤ N := by exact_mod_cast haN
  have h5 : √(a : ℝ) ≤ √(N : ℝ) := Real.sqrt_le_sqrt h4
  have h6 : (S N : ℝ) ≤ phi L b := by exact_mod_cast h1
  linarith

/-- The last entry of `a :: cs`. -/
def lastOf : ℕ → List ℕ → ℕ
  | a, [] => a
  | _, b :: rest => lastOf b rest

/-- A passing checkpoint list covers every `N` from its first to its last entry. -/
theorem chkC_sound (L : List ℕ) (h2 : ∀ q ∈ L, 2 ≤ q) (hs : L.Pairwise (· < ·))
    (hc : L.Pairwise Nat.Coprime) :
    ∀ (cs : List ℕ) (a b : ℕ), chkC L (a :: b :: cs) = true → ∀ N, a ≤ N → N ≤ lastOf b cs →
      (S N : ℝ) ≤ 0.6079 * N + 0.68 * √(N : ℝ)
  | [], a, b, h, N, h1, h3 => by
    simp only [chkC, Bool.and_eq_true] at h
    exact bound_between L h2 hs hc a b N h.1 h1 (by simpa [lastOf] using h3)
  | c :: rest, a, b, h, N, h1, h3 => by
    rw [chkC, Bool.and_eq_true] at h
    rcases le_or_gt N b with hb | hb
    · exact bound_between L h2 hs hc a b N h.1 h1 hb
    · exact chkC_sound L h2 hs hc rest b c h.2 N hb.le (by simpa [lastOf] using h3)

/-- The primes up to 661, the largest prime whose square is at most 438652. -/
def P : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661]

theorem P_two_le : ∀ q ∈ P, 2 ≤ q := by decide +kernel
theorem P_sorted : P.Pairwise (· < ·) := by decide +kernel
theorem P_coprime : P.Pairwise Nat.Coprime := by decide +kernel

end LeanLab.BS2022GRH.Lemma5MuMidS70
