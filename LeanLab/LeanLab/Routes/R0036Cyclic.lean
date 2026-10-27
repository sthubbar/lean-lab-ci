/-
# R-0036, T2 salvage: the cyclic Z/k congruence for ordered k-fold prime sums

Unit U-1358, PC run 20261021T0604Z-1697. AI-written Lean code, Claude. Checked only by the
Lean kernel. Binary Goldbach is OPEN; nothing here is progress on it, and nothing here says
anything about positivity of any representation count.

Plain-math twin.
Let k be a prime, P any set of naturals, and r_k^P(N) the number of ordered k-tuples
(a_0, ..., a_{k-1}) of elements of P with a_0 + ... + a_{k-1} = N. The cyclic group Z/k acts on
these tuples by rotating the coordinates. Since k is prime, every orbit has size 1 or k, so
r_k^P(N) is congruent mod k to the number of fixed tuples. A tuple fixed by the rotation is
constant, (c, ..., c) with k c = N and c in P. Hence
  r_k^P(N) mod k = 1 if k divides N and N/k is in P, and 0 otherwise.
For k = 3 and P the primes: r_3(N) mod 3 = 1 if 3 | N and N/3 is prime, else 0.
This is Smith's congruence |X| ≡ |X^G| mod p for a p-group, used here in Mathlib's form
`Equiv.Perm.card_fixedPoints_modEq`. It is the same orbit counting that proves Cauchy's
theorem and Fermat's little theorem in the necklace proof. KNOWN folklore.

PROVED here, unconditional:
* `rk_mod_prime`: the general statement for every prime k and every decidable P.
* `r3_eq_rk`: the explicit triple count `r3` agrees with `rk Nat.Prime 3`.
* `r3_mod_three`: r_3(N) mod 3 = 1 if 3 | N and N/3 is prime, else 0.
-/
import Mathlib

namespace LeanLab.Routes.R0036Cyclic

open Finset

/-- The finite set of ordered `k`-tuples from `P` summing to `N`. -/
def tuples (P : ℕ → Prop) [DecidablePred P] (k N : ℕ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset fun _ : Fin k => range (N + 1)).filter
    (fun v => (∑ i, v i) = N ∧ ∀ i, P (v i))

/-- `r_k^P(N)`, the number of ordered `k`-fold representations of `N` by elements of `P`. -/
def rk (P : ℕ → Prop) [DecidablePred P] (k N : ℕ) : ℕ := (tuples P k N).card

theorem mem_tuples (P : ℕ → Prop) [DecidablePred P] (k N : ℕ) (v : Fin k → ℕ) :
    v ∈ tuples P k N ↔ (∑ i, v i) = N ∧ ∀ i, P (v i) := by
  unfold tuples
  simp only [mem_filter, Fintype.mem_piFinset, mem_range]
  constructor
  · exact fun h => h.2
  · rintro ⟨hs, hp⟩
    refine ⟨fun i => ?_, hs, hp⟩
    have := Finset.single_le_sum (f := v) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega

/-- Rotation of a tuple preserves membership. -/
theorem rot_mem (P : ℕ → Prop) [DecidablePred P] (k N : ℕ) (v : Fin k → ℕ)
    (hv : v ∈ tuples P k N) : v ∘ finRotate k ∈ tuples P k N := by
  rw [mem_tuples] at hv ⊢
  refine ⟨?_, fun i => hv.2 _⟩
  rw [← hv.1]
  exact Equiv.sum_comp (finRotate k) v

/-- The rotation as an endomorphism of the finite type of representations. -/
def rot (P : ℕ → Prop) [DecidablePred P] (k N : ℕ) : Function.End (tuples P k N) :=
  fun v => ⟨v.1 ∘ finRotate k, rot_mem P k N v.1 v.2⟩

theorem rot_pow_val (P : ℕ → Prop) [DecidablePred P] (k N : ℕ) (n : ℕ)
    (v : tuples P k N) : ((rot P k N ^ n) v).1 = v.1 ∘ ⇑(finRotate k ^ n) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ']
    change ((rot P k N ^ n) (rot P k N v)).1 = _
    rw [ih]
    rfl

theorem finRotate_pow_self (k : ℕ) (hk : 2 ≤ k) : finRotate k ^ k = 1 := by
  have h := Equiv.Perm.lcm_cycleType (finRotate k)
  rw [cycleType_finRotate_of_le hk] at h
  simp at h
  have h2 := pow_orderOf_eq_one (finRotate k)
  rwa [← h] at h2

theorem rot_pow_self (P : ℕ → Prop) [DecidablePred P] (k N : ℕ) (hk : 2 ≤ k) :
    rot P k N ^ k = 1 := by
  funext v
  apply Subtype.ext
  rw [rot_pow_val, finRotate_pow_self k hk]
  rfl

/-- A tuple fixed by the rotation is constant. -/
theorem const_of_fixed (k : ℕ) (hk : 2 ≤ k) (v : Fin k → ℕ) (hv : v ∘ finRotate k = v)
    (i j : Fin k) : v i = v j := by
  have hpow : ∀ n : ℕ, v ∘ ⇑(finRotate k ^ n) = v := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.coe_mul, ← Function.comp_assoc, hv, ih]
  have hcyc := isCycle_finRotate_of_le hk
  have hsupp := support_finRotate_of_le hk
  obtain ⟨n, hn⟩ := hcyc.exists_pow_eq (x := j) (y := i)
    (by rw [← Equiv.Perm.mem_support, hsupp]; exact mem_univ _)
    (by rw [← Equiv.Perm.mem_support, hsupp]; exact mem_univ _)
  rw [← hn]
  exact congrFun (hpow n) j

theorem sum_const_fin (k c : ℕ) : (∑ _i : Fin k, c) = k * c := by
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

open Classical in
/-- The fixed point count: one if `k ∣ N` and `N / k ∈ P`, otherwise zero. -/
theorem card_fixed (P : ℕ → Prop) [DecidablePred P] (k N : ℕ) (hk : 2 ≤ k) :
    Fintype.card (Function.fixedPoints (rot P k N)) = if k ∣ N ∧ P (N / k) then 1 else 0 := by
  have hfix : ∀ v : tuples P k N, v ∈ Function.fixedPoints (rot P k N) →
      ∀ i, v.1 i = N / k ∧ k * (N / k) = N ∧ P (N / k) := by
    intro v hv i
    have hv' : v.1 ∘ finRotate k = v.1 := congrArg Subtype.val hv
    have hc := const_of_fixed k hk v.1 hv'
    have hmem := (mem_tuples P k N v.1).mp v.2
    have hsum : k * v.1 i = N := by
      have h1 : (∑ j, v.1 j) = ∑ _j : Fin k, v.1 i := Finset.sum_congr rfl (fun j _ => hc j i)
      rw [sum_const_fin] at h1
      exact h1.symm.trans hmem.1
    have hkpos : 0 < k := by omega
    have hq : N / k = v.1 i := by
      apply Nat.div_eq_of_eq_mul_left hkpos
      rw [mul_comm]; exact hsum.symm
    refine ⟨hq.symm, Nat.mul_div_cancel' (Dvd.intro _ hsum), ?_⟩
    have hp := hmem.2 i
    rw [← hq] at hp
    exact hp
  split_ifs with h
  · obtain ⟨hd, hP⟩ := h
    have hcm : (fun _ : Fin k => N / k) ∈ tuples P k N := by
      rw [mem_tuples, sum_const_fin]
      exact ⟨Nat.mul_div_cancel' hd, fun _ => hP⟩
    let c : tuples P k N := ⟨_, hcm⟩
    have hcfix : c ∈ Function.fixedPoints (rot P k N) := by
      show rot P k N c = c
      apply Subtype.ext; rfl
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨c, hcfix⟩, fun w => ?_⟩
    apply Subtype.ext; apply Subtype.ext; funext i
    exact (hfix w.1 w.2 i).1
  · rw [Fintype.card_eq_zero_iff]
    refine ⟨fun w => h ?_⟩
    have hk0 : 0 < k := by omega
    obtain ⟨_, h2, h3⟩ := hfix w.1 w.2 ⟨0, hk0⟩
    exact ⟨⟨N / k, h2.symm⟩, h3⟩

/-- **Cyclic congruence.** For a prime `k` and any `P`, `r_k^P(N) mod k` is `1` if `k ∣ N` and
`N / k ∈ P`, and `0` otherwise. -/
theorem rk_mod_prime (P : ℕ → Prop) [DecidablePred P] (k N : ℕ) (hk : k.Prime) :
    rk P k N % k = if k ∣ N ∧ P (N / k) then 1 else 0 := by
  classical
  have : Fact k.Prime := ⟨hk⟩
  have h2 : 2 ≤ k := hk.two_le
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := rot P k N) (p := k) (n := 1)
    (by rw [pow_one]; exact rot_pow_self P k N h2)
  have hc : rk P k N = Fintype.card (tuples P k N) := (Fintype.card_coe _).symm
  rw [hc]
  have e : Fintype.card (tuples P k N) % k = (if k ∣ N ∧ P (N / k) then 1 else 0) % k := by
    refine hmod.trans ?_
    show _ % k = _ % k
    congr 1
    convert card_fixed P k N h2
  rw [e]
  split_ifs
  · exact Nat.mod_eq_of_lt hk.one_lt
  · rfl

/-- The explicit ordered prime triple count `r_3(N)`. -/
def r3 (N : ℕ) : ℕ :=
  ((range (N + 1) ×ˢ range (N + 1) ×ˢ range (N + 1)).filter
    (fun t => t.1 + t.2.1 + t.2.2 = N ∧ t.1.Prime ∧ t.2.1.Prime ∧ t.2.2.Prime)).card

theorem r3_eq_rk (N : ℕ) : r3 N = rk Nat.Prime 3 N := by
  unfold r3 rk
  symm
  apply Finset.card_nbij' (fun v => (v 0, v 1, v 2)) (fun t => ![t.1, t.2.1, t.2.2])
  · intro v hv
    rw [Finset.mem_coe, mem_tuples, Fin.sum_univ_three, Fin.forall_fin_succ,
      Fin.forall_fin_succ, Fin.forall_fin_succ] at hv
    simp only [Finset.mem_coe, mem_filter, mem_product, mem_range]
    refine ⟨⟨by omega, by omega, by omega⟩, hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1⟩
  · intro t ht
    simp only [Finset.mem_coe, mem_filter, mem_product, mem_range] at ht
    rw [Finset.mem_coe, mem_tuples, Fin.sum_univ_three, Fin.forall_fin_succ,
      Fin.forall_fin_succ, Fin.forall_fin_succ]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Fin.succ_zero_eq_one, Fin.succ_one_eq_two, IsEmpty.forall_iff]
    exact ⟨ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2, trivial⟩
  · intro v _
    funext i; fin_cases i <;> rfl
  · intro t _
    rfl

/-- **The ternary cyclic congruence.** `r_3(N) mod 3 = 1` iff `3 ∣ N` and `N / 3` is prime. -/
theorem r3_mod_three (N : ℕ) : r3 N % 3 = if 3 ∣ N ∧ (N / 3).Prime then 1 else 0 := by
  rw [r3_eq_rk]; exact rk_mod_prime Nat.Prime 3 N Nat.prime_three

theorem r3_mod_three_eq_one_iff (N : ℕ) : r3 N % 3 = 1 ↔ 3 ∣ N ∧ (N / 3).Prime := by
  rw [r3_mod_three]; split_ifs with h <;> simp [h]

/-- A nonzero residue forces a representation, here the constant one. -/
theorem r3_pos_of_mod (N : ℕ) (h : r3 N % 3 ≠ 0) : 0 < r3 N := by
  rcases Nat.eq_zero_or_pos (r3 N) with h0 | h0
  · rw [h0] at h; simp at h
  · exact h0

/-! Vacuity checks: both branches of the hypothesis occur. -/

/-- `N = 9`, `9 / 3 = 3` prime: residue 1. Indeed `r3 9 = 4`. -/
example : r3 9 % 3 = 1 := (r3_mod_three_eq_one_iff 9).mpr ⟨by norm_num, by norm_num⟩

/-- `N = 15`, `15 / 3 = 5` prime: residue 1. Indeed `r3 15 = 10`. -/
example : r3 15 % 3 = 1 := (r3_mod_three_eq_one_iff 15).mpr ⟨by norm_num, by norm_num⟩

/-- `N = 12`, `12 / 3 = 4` composite: residue 0, although `12 = 2 + 5 + 5`. -/
example : r3 12 % 3 = 0 := by rw [r3_mod_three]; norm_num

/-- `k = 5`: `r_5(25) ≡ 1 mod 5` since `25 / 5 = 5` is prime. -/
example : rk Nat.Prime 5 25 % 5 = 1 := by
  rw [rk_mod_prime _ _ _ (by norm_num)]; norm_num

end LeanLab.Routes.R0036Cyclic
