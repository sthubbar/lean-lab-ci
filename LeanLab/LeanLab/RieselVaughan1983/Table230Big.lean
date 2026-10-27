/-
P0032 Riesel-Vaughan 1983, (2.30) second value, `T(99989) ≤ 80096031`, reduced to kernel facts.
Unit U-6740, CLOUD 20261020T2113Z-cloud51, track T1. AI-written Lean code, Claude. Checked only
by the Lean kernel. Binary Goldbach is OPEN.

Method. With `M = 2^40` and an integer weight `W h ≥ M · wt h` for every `h ≥ 1`, the sum
`Σ_{a<b} W (b - a)` over odd primes up to `u = 99989` is read off as one base `X = 2^128` digit of
the product of three packed numbers `A · B · E`, where `A = Σ_{a∈S} X^(u-a)`, `B = Σ_{b∈S} X^b`,
`E = Σ_{h even, 0<h≤u} W h · X^(u-h)`. GMP multiplication in the kernel replaces the 4.6·10⁷ pairs.
* `isPg_iff`: a gcd test against the primorial of the primes below 317 is `Nat.Prime` below 100489.
* `ok_spec`: a checked factor list gives the odd prime factors exactly; the list itself is found by
  an untrusted gcd tree, so a wrong list can only cost tightness, never soundness.
* `wt_mul_le_W`: `wt h · M ≤ W h` for every `h > 0`.
* `digit_eq`: digit extraction from a packed sum with total coefficient below `X`.
* `chunk_eq`, `pairs_eq_chunks`: `E` is cut into 25 blocks of 4096 digits, one kernel check each,
  and `A`, `B` are built by a sieve of geometric series joined with `|||`.
* `table230Big_of_eval`: `Table230Big` from `As_eq`, `Bs_eq` and the block sum, all three proved
  by `decide +kernel` in `Table230BigEval`.
-/
import LeanLab.RieselVaughan1983.Table230Small

open Finset

namespace LeanLab.RieselVaughan1983.Table230Big

open LeanLab.RieselVaughan1983 LeanLab.RieselVaughan1983.Table230Small

/-! ### A gcd primality test below `317²` -/

/-- The primes below 317, as a literal. -/
def spL : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
  73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173,
  179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277,
  281, 283, 293, 307, 311, 313]

/-- Their product. -/
def P : ℕ := 61076929465933196099278943388997855150356143888238371488665496574810764573680243467182799164806563626522181311132959748531230210

lemma spL_eq : spL = smallPrimes := by decide +kernel

lemma P_eq : spL.prod = P := by decide +kernel

lemma spL_lt : ∀ p ∈ spL, p < 317 := by decide +kernel

/-- Primality test: list lookup below 317, coprimality with `P` above. -/
def isPg (n : ℕ) : Bool := if n < 317 then spL.contains n else Nat.beq (Nat.gcd n P) 1

theorem isPg_iff {n : ℕ} (hn : n < 100489) : isPg n = true ↔ n.Prime := by
  unfold isPg
  split_ifs with h
  · rw [List.contains_iff_mem, spL_eq]
    exact ⟨smallPrimes_prime n, smallPrimes_complete n h⟩
  · rw [Nat.beq_eq]
    constructor
    · intro hg
      by_contra hnp
      have hn1 : n ≠ 1 := by omega
      have hm := Nat.minFac_prime hn1
      have hsq := Nat.minFac_sq_le_self (by omega) hnp
      have hle : n.minFac < 317 := by
        by_contra hc
        have : 317 * 317 ≤ n.minFac ^ 2 := by
          rw [pow_two]; exact Nat.mul_le_mul (by omega) (by omega)
        omega
      have hmem := smallPrimes_complete _ hle hm
      have h1 : n.minFac ∣ P := by
        rw [← P_eq, spL_eq]; exact List.dvd_prod hmem
      have h2 : n.minFac ∣ Nat.gcd n P := Nat.dvd_gcd (Nat.minFac_dvd n) h1
      rw [hg] at h2
      exact hm.one_lt.ne' (Nat.dvd_one.1 h2)
    · intro hp
      have : Nat.Coprime n P := by
        rw [Nat.Prime.coprime_iff_not_dvd hp, ← P_eq]
        intro hd
        obtain ⟨q, hq, hnq⟩ := (Prime.dvd_prod_iff hp.prime).1 hd
        have hq' : q.Prime := smallPrimes_prime q (spL_eq ▸ hq)
        have := (Nat.prime_dvd_prime_iff_eq hp hq').1 hnq
        have := spL_lt q hq
        omega
      exact this

/-! ### Odd prime factors from a checked list -/

/-- A binary tree of primes with the product at each node, for the untrusted factor search. -/
inductive PT
  | leaf (p : ℕ)
  | node (q : ℕ) (l r : PT)

/-- Untrusted: the leaves of the tree dividing `g`, prepended to `acc`. -/
def splitT : PT → ℕ → List ℕ → List ℕ
  | .leaf p, g, acc => if Nat.beq (g % p) 0 then p :: acc else acc
  | .node q l r, g, acc => if Nat.beq (Nat.gcd g q) 1 then acc else splitT l g (splitT r g acc)

/-- The tree over the 65 primes below 317. -/
def tree : PT :=
  PT.node 61076929465933196099278943388997855150356143888238371488665496574810764573680243467182799164806563626522181311132959748531230210
    (PT.node 525896479052627740771371797072411912900610967452630
    (PT.node 32589158477190044730
    (PT.node 9699690
    (PT.node 210
    (PT.node 6
    (PT.leaf 2)
    (PT.leaf 3))
    (PT.node 35
    (PT.leaf 5)
    (PT.leaf 7)))
    (PT.node 46189
    (PT.node 143
    (PT.leaf 11)
    (PT.leaf 13))
    (PT.node 323
    (PT.leaf 17)
    (PT.leaf 19))))
    (PT.node 3359814435017
    (PT.node 765049
    (PT.node 667
    (PT.leaf 23)
    (PT.leaf 29))
    (PT.node 1147
    (PT.leaf 31)
    (PT.leaf 37)))
    (PT.node 4391633
    (PT.node 1763
    (PT.leaf 41)
    (PT.leaf 43))
    (PT.node 2491
    (PT.leaf 47)
    (PT.leaf 53)))))
    (PT.node 16137160443118396219519316344231
    (PT.node 729345064647247
    (PT.node 17120443
    (PT.node 3599
    (PT.leaf 59)
    (PT.leaf 61))
    (PT.node 4757
    (PT.leaf 67)
    (PT.leaf 71)))
    (PT.node 42600829
    (PT.node 5767
    (PT.leaf 73)
    (PT.leaf 79))
    (PT.node 7387
    (PT.leaf 83)
    (PT.leaf 89))))
    (PT.node 22125549654501673
    (PT.node 107972737
    (PT.node 9797
    (PT.leaf 97)
    (PT.leaf 101))
    (PT.node 11021
    (PT.leaf 103)
    (PT.leaf 107)))
    (PT.node 204917929
    (PT.node 12317
    (PT.leaf 109)
    (PT.leaf 113))
    (PT.node 16637
    (PT.leaf 127)
    (PT.leaf 131))))))
    (PT.node 116138692496971593333337870943676723975950349736925608250718863879919358460867
    (PT.node 697874479951793629033168838113351811
    (PT.node 316773187163046517
    (PT.node 428448457
    (PT.node 19043
    (PT.leaf 137)
    (PT.leaf 139))
    (PT.node 22499
    (PT.leaf 149)
    (PT.leaf 151)))
    (PT.node 739349581
    (PT.node 25591
    (PT.leaf 157)
    (PT.leaf 163))
    (PT.node 28891
    (PT.leaf 167)
    (PT.leaf 173))))
    (PT.node 2203073076360437783
    (PT.node 1194324337
    (PT.node 32399
    (PT.leaf 179)
    (PT.leaf 181))
    (PT.node 36863
    (PT.leaf 191)
    (PT.leaf 193)))
    (PT.node 1844618759
    (PT.node 39203
    (PT.leaf 197)
    (PT.leaf 199))
    (PT.node 47053
    (PT.leaf 211)
    (PT.leaf 223)))))
    (PT.node 166417738194114776279230549952513744143297
    (PT.node 11835723133129382101
    (PT.node 2894777321
    (PT.node 51983
    (PT.leaf 227)
    (PT.leaf 229))
    (PT.node 55687
    (PT.leaf 233)
    (PT.leaf 239)))
    (PT.node 4088647181
    (PT.node 60491
    (PT.leaf 241)
    (PT.leaf 251))
    (PT.node 67591
    (PT.leaf 257)
    (PT.leaf 263))))
    (PT.node 14060631219760012129597
    (PT.node 5674239463
    (PT.node 72899
    (PT.leaf 269)
    (PT.leaf 271))
    (PT.node 77837
    (PT.leaf 277)
    (PT.leaf 281)))
    (PT.node 2477976354619
    (PT.node 82919
    (PT.leaf 283)
    (PT.leaf 293))
    (PT.node 29884301
    (PT.leaf 307)
    (PT.node 97343
    (PT.leaf 311)
    (PT.leaf 313)))))))

/-- Untrusted: the odd prime factors of `h`, small ones by the tree, then the one large cofactor. -/
def facL (h : ℕ) : List ℕ :=
  let g := Nat.gcd h P
  let q := h / Nat.gcd h (g ^ 17)
  (splitT tree g []).filter (fun p => !Nat.beq p 2) ++ (if Nat.blt 1 q then [q] else [])

/-- The check that makes `ps` the odd prime factor set of `h`. -/
def okB (h : ℕ) (ps : List ℕ) : Bool :=
  ps.all (fun p => Nat.ble 3 p && Nat.blt p 100489 && isPg p && Nat.beq (h % p) 0) &&
    Nat.beq ((2 * ps.prod) ^ 17 % h) 0 && decide ps.Nodup

theorem ok_spec {h : ℕ} {ps : List ℕ} (hh : 0 < h) (hok : okB h ps = true) :
    h.primeFactors.filter (2 < ·) = ps.toFinset ∧ ps.Nodup ∧ ∀ p ∈ ps, 3 ≤ p := by
  unfold okB at hok
  simp only [Bool.and_eq_true, List.all_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.beq_eq,
    decide_eq_true_eq] at hok
  obtain ⟨⟨hall, hpow⟩, hnd⟩ := hok
  have hpr : ∀ p ∈ ps, p.Prime := fun p hp => (isPg_iff (hall p hp).1.1.2).1 (hall p hp).1.2
  refine ⟨?_, hnd, fun p hp => (hall p hp).1.1.1⟩
  ext p
  simp only [mem_filter, Nat.mem_primeFactors, List.mem_toFinset]
  constructor
  · rintro ⟨⟨hp, hpd, -⟩, h2⟩
    have hd : p ∣ (2 * ps.prod) ^ 17 :=
      hpd.trans (Nat.dvd_of_mod_eq_zero hpow)
    have hd2 := hp.dvd_of_dvd_pow hd
    rcases (Nat.Prime.dvd_mul hp).1 hd2 with h2' | h2'
    · have := Nat.le_of_dvd (by norm_num) h2'; omega
    · obtain ⟨q, hq, hpq⟩ := (Prime.dvd_prod_iff hp.prime).1 h2'
      rwa [(Nat.prime_dvd_prime_iff_eq hp (hpr q hq)).1 hpq]
  · intro hp
    have := hall p hp
    exact ⟨⟨hpr p hp, Nat.dvd_of_mod_eq_zero this.2, by omega⟩, by omega⟩

/-! ### The integer weight -/

/-- The ceiling chain `x ↦ ⌈x (p - 1)/(p - 2)⌉` along `ps`. -/
def chain (x : ℕ) : List ℕ → ℕ
  | [] => x
  | p :: ps => chain ((x * (p - 1) + (p - 3)) / (p - 2)) ps

/-- The scale. -/
def M : ℕ := 2 ^ 40

/-- The weight, `⌈M · wt h⌉` up to rounding, with the sound fallback `M · h`. -/
def W (h : ℕ) : ℕ :=
  if okB h (facL h) && Nat.ble (chain M (facL h)) (M * h) then chain M (facL h) else M * h

lemma W_le (h : ℕ) : W h ≤ M * h := by
  unfold W
  split_ifs with hc
  · simp only [Bool.and_eq_true, Nat.ble_eq] at hc; exact hc.2
  · exact le_rfl

/-- The factor of (2.27). -/
noncomputable def fr (p : ℕ) : ℝ := ((p : ℝ) - 1) / ((p : ℝ) - 2)

lemma fr_nonneg {p : ℕ} (hp : 3 ≤ p) : 0 ≤ fr p := by
  unfold fr
  have : (3 : ℝ) ≤ p := by exact_mod_cast hp
  apply div_nonneg <;> linarith

lemma ceil_div_ge (A B : ℕ) (hB : 0 < B) : A ≤ B * ((A + (B - 1)) / B) := by
  have h1 := Nat.div_add_mod (A + (B - 1)) B
  have h2 := Nat.mod_lt (A + (B - 1)) hB
  omega

lemma chain_ge (ps : List ℕ) (hps : ∀ p ∈ ps, 3 ≤ p) (x : ℕ) :
    (x : ℝ) * (ps.map fr).prod ≤ chain x ps := by
  induction ps generalizing x with
  | nil => simp [chain]
  | cons p ps ih =>
    have hp : 3 ≤ p := hps p (by simp)
    have ih' := ih (fun q hq => hps q (by simp [hq])) ((x * (p - 1) + (p - 3)) / (p - 2))
    simp only [chain, List.map_cons, List.prod_cons]
    refine le_trans ?_ ih'
    have hnn : 0 ≤ (ps.map fr).prod := by
      apply List.prod_nonneg
      intro a ha
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ha
      exact fr_nonneg (hps q (by simp [hq]))
    rw [← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ hnn
    -- `x (p-1)/(p-2) ≤ ⌈x (p-1)/(p-2)⌉`
    set B := p - 2 with hB
    set y := (x * (p - 1) + (p - 3)) / B with hy
    have hBpos : 0 < B := by omega
    have key : x * (p - 1) ≤ B * y := by
      rw [hy, show p - 3 = B - 1 by omega]
      exact ceil_div_ge _ _ hBpos
    have key' : ((x * (p - 1) : ℕ) : ℝ) ≤ ((B * y : ℕ) : ℝ) := by exact_mod_cast key
    push_cast at key'
    have e1 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    have e2 : ((B : ℕ) : ℝ) = (p : ℝ) - 2 := by rw [hB, Nat.cast_sub (by omega)]; simp
    rw [e1, e2] at key'
    have hpos : (0 : ℝ) < (p : ℝ) - 2 := by
      have : (3 : ℝ) ≤ p := by exact_mod_cast hp
      linarith
    unfold fr
    rw [mul_div_assoc', div_le_iff₀ hpos]
    linarith

/-- `wt h ≤ h`, the fallback. -/
lemma wt_le_self {h : ℕ} (hh : 0 < h) : wt h ≤ h := by
  unfold wt
  set F := h.primeFactors.filter (2 < ·)
  have h1 : ∏ p ∈ F, (((p : ℝ) - 1) / ((p : ℝ) - 2)) ≤ ∏ p ∈ F, (p : ℝ) := by
    apply Finset.prod_le_prod₀
    · intro p hp
      have : 2 < p := (mem_filter.1 hp).2
      have : (3 : ℝ) ≤ p := by exact_mod_cast this
      apply div_nonneg <;> linarith
    · intro p hp
      have : 2 < p := (mem_filter.1 hp).2
      have h3 : (3 : ℝ) ≤ p := by exact_mod_cast this
      rw [div_le_iff₀ (by linarith)]
      nlinarith
  have h2 : ∏ p ∈ F, p ≤ h := by
    apply Nat.le_of_dvd hh
    exact (prod_dvd_prod_of_subset _ _ _ (filter_subset _ _)).trans (Nat.prod_primeFactors_dvd h)
  have h2' : (∏ p ∈ F, (p : ℝ)) ≤ h := by rw [← Nat.cast_prod]; exact_mod_cast h2
  linarith

/-- `wt h · M ≤ W h` below `100489`. -/
theorem wt_mul_le_W {h : ℕ} (hh : 0 < h) : wt h * M ≤ W h := by
  have hM : (0 : ℝ) ≤ M := by positivity
  unfold W
  split_ifs with hc
  · simp only [Bool.and_eq_true] at hc
    obtain ⟨hF, hnd, h3⟩ := ok_spec hh hc.1
    have : wt h = ((facL h).map fr).prod := by
      unfold wt; rw [hF, List.prod_toFinset _ hnd]; rfl
    rw [this, mul_comm]
    exact chain_ge _ h3 M
  · have := wt_le_self hh
    push_cast
    nlinarith

/-! ### Packing and digit extraction -/

/-- The base. -/
def X : ℕ := 2 ^ 128

/-- `Σ_{i < 2^d} f (lo + i) · X^i`, by halving. -/
def pack (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, lo => f lo
  | d + 1, lo => pack f d lo + pack f d (lo + 2 ^ d) * 2 ^ (128 * 2 ^ d)

lemma pack_eq (f : ℕ → ℕ) (d lo : ℕ) :
    pack f d lo = ∑ i ∈ range (2 ^ d), f (lo + i) * X ^ i := by
  induction d generalizing lo with
  | zero => simp [pack]
  | succ d ih =>
    rw [pack, ih, ih, pow_succ, mul_two, sum_range_add, sum_mul]
    congr 1
    apply sum_congr rfl
    intro i _
    have hX : X ^ (2 ^ d) = 2 ^ (128 * 2 ^ d) := by unfold X; rw [← pow_mul]
    rw [add_assoc, pow_add, hX]
    ring

/-- Reassembling a pack from its low and high halves, for the split kernel checks. -/
lemma pack_split (f : ℕ → ℕ) (d lo lo' x : ℕ) (hlo : lo' = lo + 2 ^ d)
    (h1 : x % 2 ^ (128 * 2 ^ d) = pack f d lo) (h2 : x >>> (128 * 2 ^ d) = pack f d lo') :
    x = pack f (d + 1) lo := by
  rw [pack, ← hlo, ← h1, ← h2, Nat.shiftRight_eq_div_pow]
  have := Nat.mod_add_div x (2 ^ (128 * 2 ^ d))
  linarith [Nat.mul_comm (2 ^ (128 * 2 ^ d)) (x / 2 ^ (128 * 2 ^ d))]

lemma pack_eq_range (f : ℕ → ℕ) (U : ℕ) (hU : U ≤ 2 ^ 17) (hf : ∀ i, U ≤ i → f i = 0) :
    pack f 17 0 = ∑ i ∈ range U, f i * X ^ i := by
  rw [pack_eq]
  simp only [Nat.zero_add]
  symm
  apply sum_subset (range_subset_range.2 hU)
  intro i _ hi
  rw [mem_range, not_lt] at hi
  rw [hf i hi, zero_mul]

/-- Digit extraction. -/
theorem digit_eq {ι : Type*} (T : Finset ι) (c e : ι → ℕ) (t Y : ℕ) (ht : 1 ≤ t)
    (hc : ∑ τ ∈ T, c τ < Y) :
    ((∑ τ ∈ T, c τ * Y ^ (e τ)) / Y ^ t) % Y = ∑ τ ∈ T.filter (e · = t), c τ := by
  have hY : 0 < Y := by omega
  set lo := ∑ τ ∈ T.filter (e · < t), c τ * Y ^ (e τ)
  set mid := ∑ τ ∈ T.filter (e · = t), c τ
  set hi := ∑ τ ∈ T.filter (fun τ => t < e τ), c τ * Y ^ (e τ - t - 1)
  have hsplit : ∑ τ ∈ T, c τ * Y ^ (e τ) = lo + Y ^ t * (mid + Y * hi) := by
    rw [← sum_filter_add_sum_filter_not T (e · < t)]
    rw [← sum_filter_add_sum_filter_not (T.filter (¬ e · < t)) (e · = t)]
    simp only [filter_filter]
    rw [mul_add, mul_sum, mul_sum, mul_sum]
    refine congrArg₂ (· + ·) rfl (congrArg₂ (· + ·) ?_ ?_)
    · apply sum_congr (filter_congr (fun τ _ => by omega))
      intro τ hτ
      rw [mem_filter] at hτ
      rw [hτ.2, mul_comm]
    · apply sum_congr (filter_congr (fun τ _ => by omega))
      intro τ hτ
      rw [mem_filter] at hτ
      have hk : e τ - t - 1 + (t + 1) = e τ := by omega
      calc c τ * Y ^ e τ = c τ * Y ^ (e τ - t - 1 + (t + 1)) := by rw [hk]
        _ = Y ^ t * (Y * (c τ * Y ^ (e τ - t - 1))) := by ring
  have hlo : lo < Y ^ t := by
    calc lo ≤ ∑ τ ∈ T.filter (e · < t), c τ * Y ^ (t - 1) := by
          apply sum_le_sum
          intro τ hτ
          rw [mem_filter] at hτ
          exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hY (by omega))
      _ = (∑ τ ∈ T.filter (e · < t), c τ) * Y ^ (t - 1) := by rw [sum_mul]
      _ ≤ (∑ τ ∈ T, c τ) * Y ^ (t - 1) :=
          Nat.mul_le_mul_right _ (sum_le_sum_of_subset (filter_subset _ _))
      _ < Y * Y ^ (t - 1) := Nat.mul_lt_mul_of_pos_right hc (by positivity)
      _ = Y ^ t := by rw [← pow_succ']; congr 1; omega
  have hmid : mid < Y := lt_of_le_of_lt (sum_le_sum_of_subset (filter_subset _ _)) hc
  rw [hsplit, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlo, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hmid]

/-! ### The three packed numbers for `u = 99989` -/

/-- `A`: digit `i` is `1` when `99989 - i` is an odd prime. -/
def fa (i : ℕ) : ℕ := if isPg (99989 - i) && Nat.ble 3 (99989 - i) then 1 else 0

/-- `B`: digit `j` is `1` when `j` is an odd prime up to 99989. -/
def fb (j : ℕ) : ℕ := if Nat.ble j 99989 && isPg j && Nat.ble 3 j then 1 else 0

/-- `E`: digit `k` is `W (99989 - k)` when that difference is even and positive. -/
def fe (k : ℕ) : ℕ :=
  if Nat.ble k 99989 && Nat.beq ((99989 - k) % 2) 0 && Nat.blt 0 (99989 - k) then
    W (99989 - k) else 0

/-- The even positive differences. -/
def Hs : Finset ℕ := (range 99990).filter (fun h => h % 2 = 0 ∧ 0 < h)

lemma mem_oddPrimes' {a : ℕ} : a ∈ oddPrimes 99989 ↔ a < 99990 ∧ isPg a = true ∧ 3 ≤ a := by
  rw [mem_oddPrimes]
  constructor
  · rintro ⟨h3, hu, hp⟩; exact ⟨by omega, (isPg_iff (by omega)).2 hp, h3⟩
  · rintro ⟨hu, hp, h3⟩; exact ⟨h3, by omega, (isPg_iff (by omega)).1 hp⟩

lemma packA : pack fa 17 0 = ∑ a ∈ oddPrimes 99989, X ^ (99989 - a) := by
  rw [pack_eq_range fa 99990 (by norm_num) (fun i hi => by
    unfold fa; rw [show 99989 - i = 0 by omega]; rfl)]
  have : ∀ i ∈ range 99990, fa i * X ^ i = if 99989 - i ∈ oddPrimes 99989 then X ^ i else 0 := by
    intro i hi
    rw [mem_range] at hi
    unfold fa
    by_cases hc : 99989 - i ∈ oddPrimes 99989
    · rw [if_pos hc]
      rw [mem_oddPrimes'] at hc
      simp [hc.2.1, hc.2.2]
    · rw [if_neg hc]
      rw [mem_oddPrimes'] at hc
      have : ¬ (isPg (99989 - i) = true ∧ 3 ≤ 99989 - i) := fun h => hc ⟨by omega, h⟩
      simp only [Bool.and_eq_true, Nat.ble_eq] at *
      rw [if_neg this, zero_mul]
  rw [sum_congr rfl this, ← sum_filter]
  apply sum_nbij' (fun i => 99989 - i) (fun a => 99989 - a)
  · intro i hi
    simp only [mem_filter, mem_range, mem_coe] at hi ⊢
    exact hi.2
  · intro a ha
    simp only [mem_filter, mem_range, mem_coe] at ha ⊢
    have := (mem_oddPrimes'.1 ha).1
    refine ⟨by omega, ?_⟩
    rwa [show 99989 - (99989 - a) = a by omega]
  · intro i hi
    simp only [mem_filter, mem_range, mem_coe] at hi
    omega
  · intro a ha
    have := (mem_oddPrimes'.1 ha).1
    omega
  · intro i hi
    simp only [mem_filter, mem_range, mem_coe] at hi
    rw [show 99989 - (99989 - i) = i by omega]

lemma packB : pack fb 17 0 = ∑ b ∈ oddPrimes 99989, X ^ b := by
  rw [pack_eq_range fb 99990 (by norm_num) (fun i hi => by
    unfold fb; simp only [Bool.and_eq_true, Nat.ble_eq]; rw [if_neg (by omega)])]
  have : ∀ j ∈ range 99990, fb j * X ^ j = if j ∈ oddPrimes 99989 then X ^ j else 0 := by
    intro j hj
    rw [mem_range] at hj
    unfold fb
    by_cases hc : j ∈ oddPrimes 99989
    · rw [if_pos hc]
      rw [mem_oddPrimes'] at hc
      simp [hc.2.1, hc.2.2, show j ≤ 99989 by omega]
    · rw [if_neg hc]
      rw [mem_oddPrimes'] at hc
      have : ¬ (j ≤ 99989 ∧ isPg j = true ∧ 3 ≤ j) := fun h => hc ⟨hj, h.2⟩
      simp only [Bool.and_eq_true, Nat.ble_eq, and_assoc] at *
      rw [if_neg this, zero_mul]
  rw [sum_congr rfl this, ← sum_filter]
  apply sum_congr _ (fun _ _ => rfl)
  ext b
  simp only [mem_filter, mem_range]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨(mem_oddPrimes'.1 h).1, h⟩

/-- The block of differences `h` with `u - h ∈ [lo, lo + 4096)`. -/
def Hblk (lo : ℕ) : Finset ℕ := Hs.filter (fun h => lo ≤ 99989 - h ∧ 99989 - h < lo + 4096)

lemma packE_blk (lo : ℕ) :
    pack fe 12 lo = ∑ h ∈ Hblk lo, W h * X ^ (99989 - h - lo) := by
  rw [pack_eq]
  have : ∀ i ∈ range (2 ^ 12), fe (lo + i) * X ^ i =
      if 99989 - (lo + i) ∈ Hs then W (99989 - (lo + i)) * X ^ i else 0 := by
    intro i _
    unfold fe Hs
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq, Nat.blt_eq, mem_filter, mem_range]
    by_cases hc : lo + i ≤ 99989 ∧ (99989 - (lo + i)) % 2 = 0 ∧ 0 < 99989 - (lo + i)
    · rw [if_pos ⟨⟨hc.1, hc.2.1⟩, hc.2.2⟩, if_pos ⟨by omega, hc.2⟩]
    · rw [if_neg (by omega), if_neg (by omega), zero_mul]
  rw [sum_congr rfl this, ← sum_filter]
  apply sum_nbij' (fun i => 99989 - (lo + i)) (fun h => 99989 - h - lo)
  · intro i hi
    simp only [mem_filter, mem_range, mem_coe, Hblk, Hs] at hi ⊢
    omega
  · intro h hh
    simp only [mem_filter, mem_range, mem_coe, Hblk, Hs] at hh ⊢
    refine ⟨by omega, ?_⟩
    rw [show 99989 - (lo + (99989 - h - lo)) = h by omega]
    omega
  · intro i hi
    simp only [mem_filter, mem_range, mem_coe, Hs] at hi
    omega
  · intro h hh
    simp only [mem_coe, Hblk, Hs, mem_filter, mem_range] at hh
    omega
  · intro i hi
    simp only [mem_filter, mem_range, mem_coe, Hs] at hi
    rw [show 99989 - (99989 - (lo + i)) - lo = i by omega]

/-! ### The sieve form of `A` and `B`, compared with the packs by the kernel -/

/-- `Σ_{k < c} X^(s + st·k)` as a geometric series. -/
def geo (s st c : ℕ) : ℕ := 2 ^ (128 * s) * ((2 ^ (128 * st * c) - 1) / (2 ^ (128 * st) - 1))

/-- Odd multiples `kp`, `p ≤ k`, of the odd primes below 317, as positions `kp`. -/
def Cm : ℕ := spL.tail.foldr (fun p acc => geo (p * p) p (99989 / p - p + 1) ||| acc) 0

/-- The same at the reflected positions `u - kp`. -/
def Cmr : ℕ :=
  spL.tail.foldr (fun p acc => geo (99989 - p * (99989 / p)) p (99989 / p - p + 1) ||| acc) 0

/-- `B` by the sieve: odd `n ∈ [3, u]` minus the composites. -/
def Bs : ℕ := geo 3 2 49994 - (geo 3 2 49994 &&& Cm)

/-- `A` by the sieve, reflected. -/
def As : ℕ := geo 0 2 49994 - (geo 0 2 49994 &&& Cmr)

/-- The block value: digit `2u - 4096 j` of `A · B · E_j`. -/
def chunk (j : ℕ) : ℕ :=
  ((As * Bs * pack fe 12 (4096 * j)) >>> (128 * (2 * 99989 - 4096 * j))) % 2 ^ 128

/-- The pairs `a < b` of odd primes up to `u`. -/
def Pairs : Finset (ℕ × ℕ) := (oddPrimes 99989 ×ˢ oddPrimes 99989).filter (fun x => x.1 < x.2)

lemma odd_of_mem {a : ℕ} (ha : a ∈ oddPrimes 99989) : a % 2 = 1 := by
  rw [mem_oddPrimes] at ha
  rcases ha.2.2.eq_two_or_odd with h | h
  · omega
  · exact h

lemma triple_prod (S1 S2 H : Finset ℕ) (f g w : ℕ → ℕ) :
    (∑ a ∈ S1, X ^ f a) * (∑ b ∈ S2, X ^ b) * (∑ h ∈ H, w h * X ^ g h) =
      ∑ τ ∈ S1 ×ˢ (S2 ×ˢ H), w τ.2.2 * X ^ (f τ.1 + τ.2.1 + g τ.2.2) := by
  rw [sum_product, sum_mul_sum, sum_mul]
  refine sum_congr rfl (fun a _ => ?_)
  rw [sum_product, sum_mul]
  refine sum_congr rfl (fun b _ => ?_)
  rw [mul_sum]
  refine sum_congr rfl (fun h _ => ?_)
  rw [pow_add, pow_add]
  ring

set_option linter.constructorNameAsVariable false in
/-- Each block value is the sum of `W (b - a)` over the pairs whose `u - (b - a)` lies in block `j`. -/
theorem chunk_eq (hA : As = pack fa 17 0) (hB : Bs = pack fb 17 0) (j : ℕ) (hj : j < 25) :
    chunk j = ∑ x ∈ Pairs.filter (fun x => (99989 - (x.2 - x.1)) / 4096 = j), W (x.2 - x.1) := by
  set S := oddPrimes 99989
  set lo := 4096 * j with hlo
  have hprod : As * Bs * pack fe 12 lo =
      ∑ τ ∈ S ×ˢ (S ×ˢ Hblk lo),
        W τ.2.2 * X ^ ((99989 - τ.1) + τ.2.1 + (99989 - τ.2.2 - lo)) := by
    rewrite [hA, hB, packA, packB, packE_blk]
    exact triple_prod _ _ _ _ _ _
  have hbound : ∑ τ ∈ S ×ˢ (S ×ˢ Hblk lo), W τ.2.2 < X := by
    have hS : #S ≤ 99990 := by
      calc #S ≤ #(range 99990) := card_le_card (fun a ha => mem_range.2 (mem_oddPrimes'.1 ha).1)
        _ = 99990 := card_range _
    have hH : #(Hblk lo) ≤ 99990 := by
      calc #(Hblk lo) ≤ #(range 99990) :=
            card_le_card ((filter_subset _ _).trans (filter_subset _ _))
        _ = 99990 := card_range _
    calc ∑ τ ∈ S ×ˢ (S ×ˢ Hblk lo), W τ.2.2 ≤ ∑ τ ∈ S ×ˢ (S ×ˢ Hblk lo), M * 99989 := by
          apply sum_le_sum
          intro τ hτ
          simp only [mem_product, Hblk, Hs, mem_filter, mem_range] at hτ
          exact (W_le _).trans (Nat.mul_le_mul_left _ (by omega))
      _ = #S * (#S * #(Hblk lo)) * (M * 99989) := by
          rw [sum_const, card_product, card_product, smul_eq_mul]
      _ ≤ 99990 * (99990 * 99990) * (M * 99989) := by gcongr
      _ < X := by unfold M X; norm_num
  have hsh : (As * Bs * pack fe 12 lo) >>> (128 * (2 * 99989 - lo)) =
      (As * Bs * pack fe 12 lo) / X ^ (2 * 99989 - lo) := by
    rw [Nat.shiftRight_eq_div_pow, X, ← pow_mul]
  unfold chunk
  rw [← hlo, hsh, show (2 : ℕ) ^ 128 = X from rfl, hprod,
    digit_eq _ _ _ _ _ (by omega) hbound]
  symm
  apply sum_nbij' (fun x => (x.1, x.2, x.2 - x.1)) (fun τ => (τ.1, τ.2.1))
  · intro x hx
    simp only [Pairs, mem_filter, mem_product, Hblk, Hs,
      mem_range] at hx ⊢
    have h1 := (mem_oddPrimes'.1 hx.1.1.1).1
    have h2 := (mem_oddPrimes'.1 hx.1.1.2).1
    have o1 := odd_of_mem hx.1.1.1
    have o2 := odd_of_mem hx.1.1.2
    refine ⟨⟨hx.1.1.1, hx.1.1.2, ⟨by omega, by omega, by omega⟩, by omega, by omega⟩, by omega⟩
  · intro τ hτ
    simp only [Pairs, mem_filter, mem_product, Hblk, Hs,
      mem_range] at hτ ⊢
    have := (mem_oddPrimes'.1 hτ.1.1).1
    refine ⟨⟨⟨hτ.1.1, hτ.1.2.1⟩, by omega⟩, by omega⟩
  · intro x hx
    rfl
  · intro τ hτ
    simp only [mem_filter, mem_product, Hblk, Hs,
      mem_range] at hτ
    have := (mem_oddPrimes'.1 hτ.1.1).1
    ext <;> simp <;> omega
  · intro x hx
    rfl

/-- The pair sum split into the 25 blocks. -/
theorem pairs_eq_chunks (hA : As = pack fa 17 0) (hB : Bs = pack fb 17 0) :
    ∑ a ∈ oddPrimes 99989, ∑ b ∈ (oddPrimes 99989).filter (a < ·), W (b - a) =
      ∑ j ∈ range 25, chunk j := by
  have e1 : ∑ a ∈ oddPrimes 99989, ∑ b ∈ (oddPrimes 99989).filter (a < ·), W (b - a) =
      ∑ x ∈ Pairs, W (x.2 - x.1) := by
    unfold Pairs
    rw [sum_filter, sum_product]
    apply sum_congr rfl
    intro a _
    rw [sum_filter]
  rw [e1, ← sum_fiberwise_of_maps_to (s := Pairs) (t := range 25)
    (g := fun x => (99989 - (x.2 - x.1)) / 4096)]
  · apply sum_congr rfl
    intro j hj
    rw [chunk_eq hA hB j (mem_range.1 hj)]
  · intro x _
    rw [mem_range]
    omega

/-! ### From the kernel facts to `Table230Big` -/

/-- **`Table230Big`, CONDITIONAL ON the kernel facts** `hA`, `hB` and the block sum `hc`,
all three discharged by `decide +kernel` in `Table230BigEval`. -/
theorem table230Big_of_eval (hA : As = pack fa 17 0) (hB : Bs = pack fb 17 0)
    (hc : ∑ j ∈ range 25, chunk j ≤ 80096031 * M) : Table230Big := by
  have hsum := (pairs_eq_chunks hA hB).symm ▸ hc
  unfold Table230Big Tu
  have hM : (0 : ℝ) < M := by unfold M; positivity
  have step : ∀ a ∈ oddPrimes 99989, ∀ b ∈ (oddPrimes 99989).filter (a < ·),
      wt (b - a) ≤ (W (b - a) : ℝ) / M := by
    intro a _ b hb
    rw [mem_filter, mem_oddPrimes] at hb
    rw [le_div_iff₀ hM]
    exact wt_mul_le_W (by omega)
  calc ∑ a ∈ oddPrimes 99989, ∑ b ∈ (oddPrimes 99989).filter (a < ·), wt (b - a)
      ≤ ∑ a ∈ oddPrimes 99989, ∑ b ∈ (oddPrimes 99989).filter (a < ·), (W (b - a) : ℝ) / M :=
        sum_le_sum (fun a ha => sum_le_sum (fun b hb => step a ha b hb))
    _ = ((∑ a ∈ oddPrimes 99989, ∑ b ∈ (oddPrimes 99989).filter (a < ·), W (b - a) : ℕ) : ℝ)
          / M := by
        push_cast; rw [sum_div]; exact sum_congr rfl (fun a _ => by rw [sum_div])
    _ ≤ 80096031 := by
        rw [div_le_iff₀ hM]
        exact_mod_cast hsum

end LeanLab.RieselVaughan1983.Table230Big
