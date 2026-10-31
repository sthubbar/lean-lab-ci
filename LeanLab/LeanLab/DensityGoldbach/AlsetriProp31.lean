/-
P0085 Alsetri 2025, arXiv 2505.09648, Proposition 3.1 (Shao's Prop 3.1 with 1/2 for 5/8):
m squarefree, every prime factor ≥ 11 (so coprime to 210), f from Z_m to [0, 1] with
Σ over reduced residues > φ(m)/2; every x mod m is a + b + c with reduced a, b, c and
h(f a, f b, f c) > 0, where h(x, y, z) = xy + yz + zx - (x + y + z)/2. Base modulus 1, then the
CRT fiber step for each prime p ≥ 11 using Alsetri's Lemma 2.2 (AlsetriLemma22.lean).
The prime 7 needs the n = 6 case of Alsetri's Lemma 2.1 and is not covered here.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
-/
import LeanLab.DensityGoldbach.Prop31
import LeanLab.DensityGoldbach.AlsetriLemma22

open Finset
open scoped Pointwise

namespace LeanLab.DensityGoldbach

/-- `h(x, y, z) = xy + yz + zx - 1/2 (x + y + z)`. -/
noncomputable def hhalf (x y z : ℝ) : ℝ := x * y + y * z + z * x - 1 / 2 * (x + y + z)

/-- If `h(a, b, c) > 0` with `a, b, c ∈ [0, 1]`, then `b + c ≥ 1/2`. -/
lemma half_pair_ge (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hb1 : b ≤ 1) (hc1 : c ≤ 1)
    (h : 0 < hhalf a b c) : 1 / 2 ≤ b + c := by
  unfold hhalf at h
  by_contra hlt
  push Not at hlt
  have h1 : b * c ≤ 1 / 2 * (b + c) := by nlinarith
  have h2 : a * (b + c) ≤ 1 / 2 * a := by nlinarith
  nlinarith

/-- `h` only grows when each coordinate grows inside `[0, 1]`, once it is positive. -/
lemma hhalf_mono (a b c x y z : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hx1 : x ≤ 1) (hy1 : y ≤ 1) (hz1 : z ≤ 1) (hax : a ≤ x) (hby : b ≤ y) (hcz : c ≤ z)
    (h : 0 < hhalf a b c) : 0 < hhalf x y z := by
  have ha1 : a ≤ 1 := by linarith
  have hb1 : b ≤ 1 := by linarith
  have hc1 : c ≤ 1 := by linarith
  have hbc := half_pair_ge a b c ha hb hc hb1 hc1 h
  have hca := half_pair_ge b c a hb hc ha hc1 ha1 (by unfold hhalf at h ⊢; linarith)
  have hab := half_pair_ge c a b hc ha hb ha1 hb1 (by unfold hhalf at h ⊢; linarith)
  have s1 : hhalf a b c ≤ hhalf x b c := by unfold hhalf; nlinarith
  have s2 : hhalf x b c ≤ hhalf x y c := by unfold hhalf; nlinarith
  have s3 : hhalf x y c ≤ hhalf x y z := by unfold hhalf; nlinarith
  linarith

/-- `h(a, b, c) > 0` on `[0, 1]³` gives `a, b, c > 0` and `a + b + c > 3/2`. -/
lemma hhalf_concl (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (ha1 : a ≤ 1)
    (hb1 : b ≤ 1) (hc1 : c ≤ 1) (h : 0 < hhalf a b c) :
    0 < a ∧ 0 < b ∧ 0 < c ∧ 3 / 2 < a + b + c := by
  unfold hhalf at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases ha.lt_or_eq with h' | h'
    · exact h'
    · rw [← h'] at h; nlinarith
  · rcases hb.lt_or_eq with h' | h'
    · exact h'
    · rw [← h'] at h; nlinarith
  · rcases hc.lt_or_eq with h' | h'
    · exact h'
    · rw [← h'] at h; nlinarith
  · have hq : a * b + b * c + c * a ≤ (a + b + c) ^ 2 / 3 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
    have hs : 1 / 2 * (a + b + c) < (a + b + c) ^ 2 / 3 := by linarith
    have hs0 : 0 ≤ a + b + c := by linarith
    generalize a + b + c = s at hs hs0 ⊢
    by_contra hcon; push Not at hcon
    nlinarith

/-- Alsetri Prop 3.1's statement for one modulus. -/
def Half31 (m : ℕ) [NeZero m] : Prop := ∀ f : ZMod m → ℝ,
  (∀ a, 0 ≤ f a ∧ f a ≤ 1) → 1 / 2 * (m.totient : ℝ) < ∑ a ∈ unitsMod m, f a →
  ∀ x : ZMod m, ∃ a₁ ∈ unitsMod m, ∃ a₂ ∈ unitsMod m, ∃ a₃ ∈ unitsMod m,
    x = a₁ + a₂ + a₃ ∧ 0 < hhalf (f a₁) (f a₂) (f a₃)

/-- **The fiber step, 1/2 version**, `p ≥ 11` prime: three functions on `Z/p` with values
in `[0, 1]` whose sums over the nonzero residues `S₁, S₂, S₃` satisfy
`S₁S₂ + S₂S₃ + S₃S₁ > 1/2 (p - 1)(S₁ + S₂ + S₃)`, that is `h` of the averages is positive;
then every `y` is `s + t + r`, nonzero, with `h(g₁ s, g₂ t, g₃ r) > 0`. By Alsetri Lemma 2.2. -/
theorem half_prime_three (p : ℕ) [hp : Fact p.Prime] (hp11 : 11 ≤ p) (g₁ g₂ g₃ : ZMod p → ℝ)
    (hg₁ : ∀ a, 0 ≤ g₁ a ∧ g₁ a ≤ 1) (hg₂ : ∀ a, 0 ≤ g₂ a ∧ g₂ a ≤ 1)
    (hg₃ : ∀ a, 0 ≤ g₃ a ∧ g₃ a ≤ 1)
    (hsum : 1 / 2 * ((p : ℝ) - 1) * ((∑ u ∈ unitsMod p, g₁ u) + (∑ u ∈ unitsMod p, g₂ u)
        + (∑ u ∈ unitsMod p, g₃ u)) <
      (∑ u ∈ unitsMod p, g₁ u) * (∑ u ∈ unitsMod p, g₂ u)
        + (∑ u ∈ unitsMod p, g₂ u) * (∑ u ∈ unitsMod p, g₃ u)
        + (∑ u ∈ unitsMod p, g₃ u) * (∑ u ∈ unitsMod p, g₁ u))
    (y : ZMod p) : ∃ s ∈ unitsMod p, ∃ t ∈ unitsMod p, ∃ r ∈ unitsMod p,
      y = s + t + r ∧ 0 < hhalf (g₁ s) (g₂ t) (g₃ r) := by
  set U := unitsMod p with hU
  have hn : #U = p - 1 := card_unitsMod_prime p
  obtain ⟨a, hbda, hmoa, hsa, hleva⟩ := sort_seq U g₁ hg₁
  obtain ⟨b, hbdb, hmob, hsb, hlevb⟩ := sort_seq U g₂ hg₂
  obtain ⟨c, hbdc, hmoc, hsc, hlevc⟩ := sort_seq U g₃ hg₃
  rw [hn] at hbda hmoa hsa hleva hbdb hmob hsb hlevb hbdc hmoc hsc hlevc
  have hodd : Odd p := hp.out.odd_of_ne_two (by omega)
  obtain ⟨m, hm⟩ : ∃ m, p - 1 = 2 * m := ⟨(p - 1) / 2, by obtain ⟨k, hk⟩ := hodd; omega⟩
  have hm5 : 5 ≤ m := by omega
  obtain ⟨i, j, k, hi, hj, hk, hs, hlt⟩ : ∃ i j k, i < p - 1 ∧ j < p - 1 ∧ k < p - 1 ∧
      p - 1 ≤ i + j + k ∧ 1 / 2 * (a i + b j + c k) < a i * b j + b j * c k + c k * a i := by
    by_contra hne
    push Not at hne
    rw [hm] at hbda hmoa hsa hbdb hmob hsb hbdc hmoc hsc
    have := half_lemma22 m hm5 a b c hbda hbdb hbdc hmoa hmob hmoc (fun i j k hi hj hk hs =>
      hne i j k (by omega) (by omega) (by omega) (by omega))
    rw [hsa, hsb, hsc] at this
    have hn' : (p : ℝ) - 1 = 2 * m := by
      have : ((p - 1 : ℕ) : ℝ) = (2 * m : ℕ) := by rw [hm]
      push_cast at this
      rwa [Nat.cast_sub (by omega), Nat.cast_one] at this
    rw [hn'] at hsum
    linarith
  have huniv := three_levels p _ _ _ i j k (hleva i hi) (hlevb j hj) (hlevc k hk) hs
  have hx : y ∈ U.filter (fun u => a i ≤ g₁ u) + U.filter (fun u => b j ≤ g₂ u) +
      U.filter (fun u => c k ≤ g₃ u) := by rw [huniv]; exact mem_univ y
  obtain ⟨y', hy, z3, hz3, rfl⟩ := mem_add.1 hx
  obtain ⟨z1, hz1, z2, hz2, rfl⟩ := mem_add.1 hy
  obtain ⟨hz1U, hz1f⟩ := mem_filter.1 hz1
  obtain ⟨hz2U, hz2f⟩ := mem_filter.1 hz2
  obtain ⟨hz3U, hz3f⟩ := mem_filter.1 hz3
  have hh : 0 < hhalf (a i) (b j) (c k) := by unfold hhalf; linarith
  exact ⟨z1, hz1U, z2, hz2U, z3, hz3U, rfl, hhalf_mono _ _ _ _ _ _ (hbda i hi).1 (hbdb j hj).1
    (hbdc k hk).1 (hg₁ _).2 (hg₂ _).2 (hg₃ _).2 hz1f hz2f hz3f hh⟩

/-- **Shao Prop 3.1, induction step**: `Half31 m` gives `Half31 (m p)` for a prime `p ≥ 11`
coprime to `m`. -/
theorem half31_step (m p : ℕ) [NeZero m] [hp : Fact p.Prime] [NeZero (m * p)] (hp11 : 11 ≤ p)
    (hcop : m.Coprime p) (hm : Half31 m) : Half31 (m * p) := by
  intro f hf hsum x
  have : NeZero p := ⟨hp.out.ne_zero⟩
  set e := ZMod.chineseRemainder hcop with he
  set F : ZMod m → ZMod p → ℝ := fun u v => f (e.symm (u, v)) with hF
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (11 : ℝ) ≤ p := by exact_mod_cast hp11
    linarith
  have hcardp : (#(unitsMod p) : ℝ) = (p : ℝ) - 1 := by
    rw [card_unitsMod_prime p, Nat.cast_sub hp.out.one_le, Nat.cast_one]
  -- the averaged function mod `m`
  set f' : ZMod m → ℝ := fun u => (∑ v ∈ unitsMod p, F u v) / ((p : ℝ) - 1) with hf'
  have hS : ∀ u, ∑ v ∈ unitsMod p, F u v = ((p : ℝ) - 1) * f' u := by
    intro u; rw [hf']; field_simp
  have hf'bd : ∀ u, 0 ≤ f' u ∧ f' u ≤ 1 := by
    intro u
    have h0 : 0 ≤ ∑ v ∈ unitsMod p, F u v := sum_nonneg fun v _ => (hf _).1
    have h1 : ∑ v ∈ unitsMod p, F u v ≤ (p : ℝ) - 1 := by
      calc ∑ v ∈ unitsMod p, F u v ≤ ∑ v ∈ unitsMod p, (1 : ℝ) :=
            sum_le_sum fun v _ => (hf _).2
        _ = (p : ℝ) - 1 := by rw [sum_const, nsmul_one, hcardp]
    constructor
    · exact div_nonneg h0 hp1.le
    · rw [div_le_one hp1]; exact h1
  have hsum' : 1 / 2 * (m.totient : ℝ) < ∑ u ∈ unitsMod m, f' u := by
    rw [sum_unitsMod_crt hcop, Nat.totient_mul hcop, Nat.totient_prime hp.out] at hsum
    have : ∑ u ∈ unitsMod m, ∑ v ∈ unitsMod p, F u v =
        ((p : ℝ) - 1) * ∑ u ∈ unitsMod m, f' u := by
      rw [mul_sum]; exact sum_congr rfl fun u _ => hS u
    rw [this] at hsum
    push_cast at hsum
    rw [Nat.cast_sub hp.out.one_le, Nat.cast_one] at hsum
    nlinarith
  obtain ⟨a₁, ha₁, a₂, ha₂, a₃, ha₃, hx1, hh⟩ := hm f' hf'bd hsum' (e x).1
  have hpos := half_prime_three p hp11 (F a₁) (F a₂) (F a₃) (fun v => hf _) (fun v => hf _)
    (fun v => hf _) (by
      rw [hS a₁, hS a₂, hS a₃]
      unfold hhalf at hh
      have hq : 0 < ((p : ℝ) - 1) ^ 2 := by positivity
      nlinarith [mul_lt_mul_of_pos_left hh hq]) (e x).2
  obtain ⟨s, hs, t, ht, r, hr, hx2, hh2⟩ := hpos
  refine ⟨e.symm (a₁, s), ?_, e.symm (a₂, t), ?_, e.symm (a₃, r), ?_, ?_, hh2⟩
  · rw [mem_unitsMod_crt hcop, RingEquiv.apply_symm_apply]; exact ⟨ha₁, hs⟩
  · rw [mem_unitsMod_crt hcop, RingEquiv.apply_symm_apply]; exact ⟨ha₂, ht⟩
  · rw [mem_unitsMod_crt hcop, RingEquiv.apply_symm_apply]; exact ⟨ha₃, hr⟩
  · apply e.injective
    rw [map_add, map_add, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply,
      RingEquiv.apply_symm_apply, Prod.mk_add_mk, Prod.mk_add_mk, ← hx1, ← hx2]

/-- `Half31` does not depend on how the modulus is written. -/
lemma half31_congr {m n : ℕ} (h : m = n) {_ : NeZero m} {_ : NeZero n} (hm : Half31 m) :
    Half31 n := by
  subst h; exact hm

/-- The trivial modulus. -/
lemma half31_one : Half31 1 := by
  intro f hf hsum x
  have hU : (0 : ZMod 1) ∈ unitsMod 1 := mem_filter.2 ⟨mem_univ _, isUnit_of_subsingleton _⟩
  have hUe : unitsMod 1 = {0} := by
    ext u; rw [mem_singleton]
    exact ⟨fun _ => Subsingleton.elim _ _, fun h => h ▸ hU⟩
  rw [hUe, sum_singleton, Nat.totient_one, Nat.cast_one] at hsum
  refine ⟨0, hU, 0, hU, 0, hU, Subsingleton.elim _ _, ?_⟩
  unfold hhalf
  nlinarith [(hf 0).1]

/-- Induction over a finset of primes `≥ 11` coprime to the base modulus. -/
theorem half31_prod (m₀ : ℕ) [NeZero m₀] (h₀ : Half31 m₀) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ 11 ≤ p) (hcop : ∀ p ∈ S, m₀.Coprime p) :
    ∀ n (_ : n = m₀ * ∏ p ∈ S, p) (_ : NeZero n), Half31 n := by
  induction S using Finset.induction_on with
  | empty =>
    intro n hn _
    exact half31_congr (by simp [hn]) h₀
  | insert a s ha ih =>
    intro n hn _
    have hpos : ∀ p ∈ s, 0 < p := fun p hp => (hS p (mem_insert_of_mem hp)).1.pos
    have hprod : 0 < ∏ p ∈ s, p := prod_pos hpos
    have hm0 : 0 < m₀ := Nat.pos_of_ne_zero (NeZero.ne m₀)
    set k := m₀ * ∏ p ∈ s, p with hk
    have hk0 : NeZero k := ⟨(Nat.mul_pos hm0 hprod).ne'⟩
    have ih' : Half31 k := ih (fun p hp => hS p (mem_insert_of_mem hp))
      (fun p hp => hcop p (mem_insert_of_mem hp)) k rfl hk0
    obtain ⟨hap, ha11⟩ := hS a (mem_insert_self a s)
    have : Fact a.Prime := ⟨hap⟩
    have hka : NeZero (k * a) := ⟨(Nat.mul_pos (Nat.mul_pos hm0 hprod) hap.pos).ne'⟩
    have hc : k.Coprime a := by
      refine Nat.coprime_mul_iff_left.2 ⟨hcop a (mem_insert_self a s), ?_⟩
      refine Nat.Coprime.prod_left fun p hp => ?_
      obtain ⟨hpp, _⟩ := hS p (mem_insert_of_mem hp)
      exact (Nat.coprime_primes hpp hap).2 (fun h => ha (h ▸ hp))
    have step : Half31 (k * a) := half31_step k a ha11 hc ih'
    have heq : k * a = n := by rw [hn, prod_insert ha, hk]; ring
    exact half31_congr heq step


lemma prime_ge_eleven' {p : ℕ} (hp : p.Prime) (h : p.Coprime 210) : 11 ≤ p := by
  by_contra hlt
  push Not at hlt
  have h2 := hp.two_le
  interval_cases p <;> revert hp h <;> decide

/-- **Alsetri Proposition 3.1** for every squarefree `m` coprime to `210`. -/
theorem half31 (m : ℕ) [NeZero m] (hsq : Squarefree m) (h210 : m.Coprime 210) : Half31 m := by
  have hm : ∏ p ∈ m.primeFactors, p = m := Nat.prod_primeFactors_of_squarefree hsq
  have hS : ∀ p ∈ m.primeFactors, p.Prime ∧ 11 ≤ p := fun p hp =>
    ⟨Nat.prime_of_mem_primeFactors hp, prime_ge_eleven' (Nat.prime_of_mem_primeFactors hp)
      (Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hp) h210)⟩
  have he : 1 * ∏ p ∈ m.primeFactors, p = m := by rw [one_mul, hm]
  exact half31_prod 1 half31_one _ hS (fun p _ => Nat.coprime_one_left p) m he.symm inferInstance

end LeanLab.DensityGoldbach

#print axioms LeanLab.DensityGoldbach.half31
