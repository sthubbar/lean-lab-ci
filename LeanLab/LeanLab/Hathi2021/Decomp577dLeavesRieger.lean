import LeanLab.Hathi2021.Decomp577d

/-!
Rieger 1968 Satz 3, pages 94 to 96, split for Decomp577d.rieger_nontrivial_collision_bound.
DOI https://doi.org/10.1515/crll.1968.231.89, used by Hu 2019 page 195.
The nontrivial collisions of prime squares are first reduced to odd primes with no
lower cutoff, then parameterized as in Rieger display 15, and the parameterized count
is the sieve input of displays 18 to 20.
AI wrote this Lean code. Binary Goldbach is OPEN.
-/

open Finset

namespace LeanLab.Hathi2021.Decomp577dLeavesRieger

open LeanLab.Hathi2021.Decomp577d

/-- Rieger page 94, the set counted by `C x` before display 15: ordered quadruples of
odd primes up to `X` with `p₁² + p₂² = p₃² + p₄²`, excluding the two trivial matches. -/
def oddCollisions (X : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  ((range (X + 1)) ×ˢ (range (X + 1)) ×ˢ (range (X + 1)) ×ˢ (range (X + 1))).filter
    (fun q => q.1.Prime ∧ q.1 ≠ 2 ∧ q.2.1.Prime ∧ q.2.1 ≠ 2 ∧ q.2.2.1.Prime ∧ q.2.2.1 ≠ 2 ∧
      q.2.2.2.Prime ∧ q.2.2.2 ≠ 2 ∧
      q.1 ^ 2 + q.2.1 ^ 2 = q.2.2.1 ^ 2 + q.2.2.2 ^ 2 ∧
      (q.2.2.1, q.2.2.2) ≠ (q.1, q.2.1) ∧ (q.2.2.1, q.2.2.2) ≠ (q.2.1, q.1))

/-- An odd prime at most `X`. Helper predicate for the parameterization of Rieger
display 15. -/
def OddPrimeLe (X q : ℕ) : Prop := q.Prime ∧ q ≠ 2 ∧ q ≤ X

instance (X q : ℕ) : Decidable (OddPrimeLe X q) := by unfold OddPrimeLe; infer_instance

/-- Rieger page 94, display 15: from `p₁² - p₃² = p₄² - p₂²` with `p₁ > p₃`, write
`p₁ - p₃ = g u`, `p₄ - p₂ = g v` with `u, v` coprime and `p₁ + p₃ = v h`, `p₄ + p₂ = u h`.
The four primes are then `(gu + vh)/2`, `(vh - gu)/2`, `(gv + uh)/2`, `(uh - gv)/2`.
The case `u = v` is the swapped trivial match and is excluded. Tuples `(g, u, v, h)`. -/
def paramQuads (X : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  ((range (2 * X + 1)) ×ˢ (range (2 * X + 1)) ×ˢ (range (2 * X + 1)) ×ˢ
      (range (2 * X + 1))).filter
    (fun t => 0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2.1 ∧ t.2.1 ≠ t.2.2.1 ∧
      Nat.Coprime t.2.1 t.2.2.1 ∧
      t.1 * t.2.1 < t.2.2.1 * t.2.2.2 ∧ t.1 * t.2.2.1 < t.2.1 * t.2.2.2 ∧
      2 ∣ t.1 * t.2.1 + t.2.2.1 * t.2.2.2 ∧ 2 ∣ t.1 * t.2.2.1 + t.2.1 * t.2.2.2 ∧
      OddPrimeLe X ((t.1 * t.2.1 + t.2.2.1 * t.2.2.2) / 2) ∧
      OddPrimeLe X ((t.2.2.1 * t.2.2.2 - t.1 * t.2.1) / 2) ∧
      OddPrimeLe X ((t.1 * t.2.2.1 + t.2.1 * t.2.2.2) / 2) ∧
      OddPrimeLe X ((t.2.1 * t.2.2.2 - t.1 * t.2.2.1) / 2))

/-- Helper for Rieger page 94, S124: a collision with the prime 2 on the left is trivial,
by parity. -/
theorem two_collision {b c d : ℕ} (hb : b.Prime) (hc : c.Prime) (hd : d.Prime)
    (h : 2 ^ 2 + b ^ 2 = c ^ 2 + d ^ 2) : (c, d) = (2, b) ∨ (c, d) = (b, 2) := by
  have hc2 := hc.two_le
  have hd2 := hd.two_le
  rcases hb.eq_two_or_odd' with rfl | hbo
  · have hc3 : c < 3 := by nlinarith
    have hd3 : d < 3 := by nlinarith
    left
    have : c = 2 := by omega
    have : d = 2 := by omega
    subst c; subst d; rfl
  · rcases hc.eq_two_or_odd' with rfl | hco
    · left
      have : b ^ 2 = d ^ 2 := by omega
      have := Nat.pow_left_injective (n := 2) (by norm_num) this
      rw [this]
    · rcases hd.eq_two_or_odd' with rfl | hdo
      · right
        have : b ^ 2 = c ^ 2 := by omega
        have := Nat.pow_left_injective (n := 2) (by norm_num) this
        rw [this]
      · exfalso
        have he : Even (c ^ 2 + d ^ 2) := Odd.add_odd (hco.pow) (hdo.pow)
        have ho : Odd (2 ^ 2 + b ^ 2) := Even.add_odd (by decide) hbo.pow
        rw [h] at ho
        exact (Nat.not_even_iff_odd.mpr ho) he

/-- Helper for Rieger page 94, S124: a nontrivial prime square collision has no prime 2. -/
theorem no_two {a b c d : ℕ} (ha : a.Prime) (hb : b.Prime) (hc : c.Prime) (hd : d.Prime)
    (h : a ^ 2 + b ^ 2 = c ^ 2 + d ^ 2) (h1 : (c, d) ≠ (a, b)) (h2 : (c, d) ≠ (b, a)) :
    a ≠ 2 ∧ b ≠ 2 ∧ c ≠ 2 ∧ d ≠ 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro rfl
    rcases two_collision hb hc hd h with h' | h' <;> simp_all
  · rintro rfl
    rcases two_collision ha hc hd (by omega) with h' | h' <;> simp_all
  · rintro rfl
    rcases two_collision hd ha hb (by omega) with h' | h' <;>
      simp only [Prod.mk.injEq] at h' <;> obtain ⟨rfl, rfl⟩ := h' <;> simp_all
  · rintro rfl
    rcases two_collision hc ha hb (by omega) with h' | h' <;>
      simp only [Prod.mk.injEq] at h' <;> obtain ⟨rfl, rfl⟩ := h' <;> simp_all

/-- Helper for Rieger page 94, display 15, S124: the arithmetic of the parameterization. -/
theorem param_key (p1 p2 p3 p4 : ℕ) (h2 : 0 < p2) (h3 : 0 < p3) (hlt : p3 < p1)
    (heq : p1 ^ 2 + p2 ^ 2 = p3 ^ 2 + p4 ^ 2) (hnt : (p3, p4) ≠ (p2, p1)) (g u v h : ℕ)
    (hg : g = Nat.gcd (p1 - p3) (p4 - p2)) (hu : u = (p1 - p3) / g)
    (hv : v = (p4 - p2) / g) (hh : h = (p1 + p3) / v) :
    0 < g ∧ 0 < u ∧ 0 < v ∧ u ≠ v ∧ Nat.Coprime u v ∧ g * u < v * h ∧ g * v < u * h ∧
      g * u + v * h = 2 * p1 ∧ v * h - g * u = 2 * p3 ∧ g * v + u * h = 2 * p4 ∧
      u * h - g * v = 2 * p2 ∧ g ≤ p1 ∧ u ≤ p1 ∧ v ≤ p4 ∧ h ≤ p1 + p3 := by
  have hcop : Nat.Coprime u v := by
    rw [hu, hv, hg]
    exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left _ (by omega))
  obtain ⟨a, rfl⟩ : ∃ a, p1 = p3 + a := ⟨p1 - p3, by omega⟩
  have ha : 0 < a := by omega
  have hp4 : p2 < p4 := by nlinarith
  obtain ⟨b, rfl⟩ : ∃ b, p4 = p2 + b := ⟨p4 - p2, by omega⟩
  have hb : 0 < b := by omega
  have hab : a * (2 * p3 + a) = b * (2 * p2 + b) := by
    have h' : ((p3 : ℤ) + a) ^ 2 + (p2 : ℤ) ^ 2 = (p3 : ℤ) ^ 2 + ((p2 : ℤ) + b) ^ 2 := by
      exact_mod_cast heq
    have : (a : ℤ) * (2 * p3 + a) = b * (2 * p2 + b) := by linear_combination h'
    exact_mod_cast this
  simp only [Nat.add_sub_cancel_left] at hg hu hv
  have hg0 : 0 < g := by rw [hg]; exact Nat.gcd_pos_of_pos_left _ ha
  have hga : g ≤ a := by rw [hg]; exact Nat.gcd_le_left b ha
  obtain ⟨u', hu'⟩ : g ∣ a := by rw [hg]; exact Nat.gcd_dvd_left a b
  obtain ⟨v', hv'⟩ : g ∣ b := by rw [hg]; exact Nat.gcd_dvd_right a b
  have huu : u = u' := by rw [hu, hu', Nat.mul_div_cancel_left _ hg0]
  have hvv : v = v' := by rw [hv, hv', Nat.mul_div_cancel_left _ hg0]
  subst huu hvv
  subst hu' hv'
  have hu0 : 0 < u := Nat.pos_of_ne_zero (by rintro rfl; simp at ha)
  have hv0 : 0 < v := Nat.pos_of_ne_zero (by rintro rfl; simp at hb)
  have huv : u * (2 * p3 + g * u) = v * (2 * p2 + g * v) := by
    apply Nat.eq_of_mul_eq_mul_left hg0
    calc g * (u * (2 * p3 + g * u)) = g * u * (2 * p3 + g * u) := by ring
      _ = g * v * (2 * p2 + g * v) := hab
      _ = g * (v * (2 * p2 + g * v)) := by ring
  have hvd : v ∣ (2 * p3 + g * u) * u := ⟨2 * p2 + g * v, by rw [mul_comm]; exact huv⟩
  obtain ⟨h', hh'⟩ := (Nat.Coprime.symm hcop).dvd_of_dvd_mul_right hvd
  have hhh : h = h' := by
    rw [hh, show p3 + g * u + p3 = 2 * p3 + g * u by ring, hh', Nat.mul_div_cancel_left _ hv0]
  subst hhh
  have hd : 2 * p2 + g * v = u * h := by
    apply Nat.eq_of_mul_eq_mul_left hv0
    rw [← huv, hh']; ring
  have hc : 2 * p3 + g * u = v * h := hh'
  have hule : u ≤ g * u := Nat.le_mul_of_pos_left u hg0
  have hvle : v ≤ g * v := Nat.le_mul_of_pos_left v hg0
  have hhle : h ≤ v * h := Nat.le_mul_of_pos_left h hv0
  have hne : u ≠ v := by
    rintro rfl
    apply hnt
    have : p3 = p2 := by omega
    subst this
    simp only [Prod.mk.injEq, true_and] <;> omega
  refine ⟨hg0, hu0, hv0, hne, hcop, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega


/-- Helper for Rieger page 94, display 15, S124: the parameter tuple lies in `paramQuads`
and determines the four primes. -/
theorem param_mem (X p1 p2 p3 p4 : ℕ) (hp1 : OddPrimeLe X p1) (hp2 : OddPrimeLe X p2)
    (hp3 : OddPrimeLe X p3) (hp4 : OddPrimeLe X p4) (hlt : p3 < p1)
    (heq : p1 ^ 2 + p2 ^ 2 = p3 ^ 2 + p4 ^ 2) (hnt : (p3, p4) ≠ (p2, p1)) (g u v h : ℕ)
    (hg : g = Nat.gcd (p1 - p3) (p4 - p2)) (hu : u = (p1 - p3) / g)
    (hv : v = (p4 - p2) / g) (hh : h = (p1 + p3) / v) :
    (g, u, v, h) ∈ paramQuads X ∧ (g * u + v * h) / 2 = p1 ∧ (g * v + u * h) / 2 = p4 ∧
      (v * h - g * u) / 2 = p3 ∧ (u * h - g * v) / 2 = p2 := by
  obtain ⟨hq1, hn1, hl1⟩ := hp1
  obtain ⟨hq2, hn2, hl2⟩ := hp2
  obtain ⟨hq3, hn3, hl3⟩ := hp3
  obtain ⟨hq4, hn4, hl4⟩ := hp4
  obtain ⟨hk0, hk1, hk2, hk3, hk4, hk5, hk6, hk7, hk8, hk9, hk10, hk11, hk12, hk13, hk14⟩ :=
    param_key p1 p2 p3 p4 hq2.pos hq3.pos hlt heq hnt g u v h hg hu hv hh
  have e1 : (g * u + v * h) / 2 = p1 := by rw [hk7]; omega
  have e2 : (g * v + u * h) / 2 = p4 := by rw [hk9]; omega
  have e3 : (v * h - g * u) / 2 = p3 := by rw [hk8]; omega
  have e4 : (u * h - g * v) / 2 = p2 := by rw [hk10]; omega
  refine ⟨?_, e1, e2, e3, e4⟩
  refine Finset.mem_filter.mpr ⟨?_, hk0, hk1, hk2, hk3, hk4, hk5, hk6,
    ⟨p1, by rw [hk7]⟩, ⟨p4, by rw [hk9]⟩, ?_, ?_, ?_, ?_⟩
  · simp only [mem_product, mem_range]
    omega
  · show OddPrimeLe X ((g * u + v * h) / 2); rw [e1]; exact ⟨hq1, hn1, hl1⟩
  · show OddPrimeLe X ((v * h - g * u) / 2); rw [e3]; exact ⟨hq3, hn3, hl3⟩
  · show OddPrimeLe X ((g * v + u * h) / 2); rw [e2]; exact ⟨hq4, hn4, hl4⟩
  · show OddPrimeLe X ((u * h - g * v) / 2); rw [e4]; exact ⟨hq2, hn2, hl2⟩

/-- LEAF: Rieger page 94 and Satz 3, reduction of the weighted range to odd primes. Class
MEDIUM. Hu 2019 page 195. The ordered nontrivial collision count with the Hu lower cutoff is
at most the number of odd prime collisions up to `√n`: the cutoff only removes pairs, and a
collision containing the prime 2 is trivial by parity. -/
theorem collisionCount_le_oddCollisions (n₁ n : ℕ) :
    collisionCount n₁ n ≤ ((oddCollisions (Nat.sqrt n)).card : ℝ) := by
  classical
  unfold collisionCount
  simp only
  rw [← Finset.sum_product' (f := fun i j => if pairFrequency i = pairFrequency j ∧ j ≠ i ∧
    j ≠ i.swap then (1 : ℝ) else 0)]
  rw [Finset.sum_boole]
  have key : ((((squarePrimes n₁ n) ×ˢ (squarePrimes n₁ n)) ×ˢ
      ((squarePrimes n₁ n) ×ˢ (squarePrimes n₁ n))).filter
      (fun x : (ℕ × ℕ) × (ℕ × ℕ) => pairFrequency x.1 = pairFrequency x.2 ∧ x.2 ≠ x.1 ∧
        x.2 ≠ x.1.swap)).card ≤ (oddCollisions (Nat.sqrt n)).card := by
    apply Finset.card_le_card_of_injOn (fun x => (x.1.1, x.1.2, x.2.1, x.2.2))
    · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ hx
      simp only [coe_filter, Set.mem_setOf_eq, mem_product] at hx
      obtain ⟨⟨⟨ha, hb⟩, hc, hd⟩, hf, h1, h2⟩ := hx
      have hmem : ∀ p ∈ squarePrimes n₁ n, p.Prime ∧ p < Nat.sqrt n + 1 := by
        intro p hp
        have hm := Finset.mem_filter.mp hp
        exact ⟨hm.2.1, Nat.lt_succ_of_le (Nat.le_sqrt'.mpr hm.2.2.2)⟩
      obtain ⟨pa, la⟩ := hmem a ha
      obtain ⟨pb, lb⟩ := hmem b hb
      obtain ⟨pc, lc⟩ := hmem c hc
      obtain ⟨pd, ld⟩ := hmem d hd
      have heq : a ^ 2 + b ^ 2 = c ^ 2 + d ^ 2 := by
        unfold pairFrequency at hf; exact_mod_cast hf
      have h2' : (c, d) ≠ (b, a) := h2
      obtain ⟨n1, n2, n3, n4⟩ := no_two pa pb pc pd heq h1 h2'
      simp only [oddCollisions, coe_filter, Set.mem_setOf_eq, mem_product, mem_range]
      exact ⟨⟨la, lb, lc, ld⟩, pa, n1, pb, n2, pc, n3, pd, n4, heq, h1, h2'⟩
    · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ _ ⟨⟨a', b'⟩, ⟨c', d'⟩⟩ _ hxy
      simp only [Prod.mk.injEq] at hxy
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hxy
      rfl
  exact_mod_cast key

/-- LEAF: Rieger page 94, display 15, the parameterization. Class MEDIUM. Each odd prime
collision with `p₁ > p₃` gives one tuple of `paramQuads`, with `g = gcd`; the case
`p₁ < p₃` is the same after exchanging the two sides, giving the factor 2. -/
theorem oddCollisions_le_paramQuads (X : ℕ) :
    (oddCollisions X).card ≤ 2 * (paramQuads X).card := by
  classical
  let F : ℕ × ℕ × ℕ × ℕ → ℕ × ℕ × ℕ × ℕ := fun q =>
    (Nat.gcd (q.1 - q.2.2.1) (q.2.2.2 - q.2.1),
      (q.1 - q.2.2.1) / Nat.gcd (q.1 - q.2.2.1) (q.2.2.2 - q.2.1),
      (q.2.2.2 - q.2.1) / Nat.gcd (q.1 - q.2.2.1) (q.2.2.2 - q.2.1),
      (q.1 + q.2.2.1) / ((q.2.2.2 - q.2.1) / Nat.gcd (q.1 - q.2.2.1) (q.2.2.2 - q.2.1)))
  have hunpack : ∀ q ∈ oddCollisions X, OddPrimeLe X q.1 ∧ OddPrimeLe X q.2.1 ∧
      OddPrimeLe X q.2.2.1 ∧ OddPrimeLe X q.2.2.2 ∧
      q.1 ^ 2 + q.2.1 ^ 2 = q.2.2.1 ^ 2 + q.2.2.2 ^ 2 ∧
      (q.2.2.1, q.2.2.2) ≠ (q.1, q.2.1) ∧ (q.2.2.1, q.2.2.2) ≠ (q.2.1, q.1) := by
    intro q hq
    obtain ⟨hr, pa, na, pb, nb, pc, nc, pd, nd, heq, h1, h2⟩ := Finset.mem_filter.mp hq
    simp only [mem_product, mem_range] at hr
    obtain ⟨la, lb, lc, ld⟩ := hr
    exact ⟨⟨pa, na, by omega⟩, ⟨pb, nb, by omega⟩, ⟨pc, nc, by omega⟩, ⟨pd, nd, by omega⟩,
      heq, h1, h2⟩
  have hA : ((oddCollisions X).filter (fun q => q.2.2.1 < q.1)).card ≤ (paramQuads X).card := by
    apply Finset.card_le_card_of_injOn F
    · intro q hq
      have hq := Finset.mem_filter.mp hq
      obtain ⟨h1, h2, h3, h4, heq, -, hnt⟩ := hunpack _ hq.1
      exact (param_mem X q.1 q.2.1 q.2.2.1 q.2.2.2 h1 h2 h3 h4 hq.2 heq hnt
        (F q).1 (F q).2.1 (F q).2.2.1 (F q).2.2.2 rfl rfl rfl rfl).1
    · intro q hq q' hq' hF
      have hq := Finset.mem_filter.mp hq
      have hq' := Finset.mem_filter.mp hq'
      obtain ⟨h1, h2, h3, h4, heq, -, hnt⟩ := hunpack _ hq.1
      obtain ⟨h1', h2', h3', h4', heq', -, hnt'⟩ := hunpack _ hq'.1
      obtain ⟨-, e1, e2, e3, e4⟩ := param_mem X q.1 q.2.1 q.2.2.1 q.2.2.2 h1 h2 h3 h4 hq.2 heq
        hnt (F q).1 (F q).2.1 (F q).2.2.1 (F q).2.2.2 rfl rfl rfl rfl
      obtain ⟨-, e1', e2', e3', e4'⟩ := param_mem X q'.1 q'.2.1 q'.2.2.1 q'.2.2.2 h1' h2' h3'
        h4' hq'.2 heq' hnt' (F q').1 (F q').2.1 (F q').2.2.1 (F q').2.2.2 rfl rfl rfl rfl
      have hF' : F q = F q' := hF
      rw [hF'] at e1 e2 e3 e4
      obtain ⟨a, b, c, d⟩ := q
      obtain ⟨a', b', c', d'⟩ := q'
      simp only at e1 e2 e3 e4 e1' e2' e3' e4'
      rw [← e1, ← e2, ← e3, ← e4, e1', e2', e3', e4']
  have hB : ((oddCollisions X).filter (fun q => ¬ q.2.2.1 < q.1)).card ≤
      ((oddCollisions X).filter (fun q => q.2.2.1 < q.1)).card := by
    apply Finset.card_le_card_of_injOn (fun q => (q.2.2.1, q.2.2.2, q.1, q.2.1))
    · rintro ⟨a, b, c, d⟩ hq
      have hq := Finset.mem_filter.mp hq
      obtain ⟨h1, h2, h3, h4, heq, hnt1, hnt⟩ := hunpack _ hq.1
      simp only at h1 h2 h3 h4 heq hnt1 hnt
      have hlt : a < c := by
        rcases Nat.lt_or_ge a c with h | h
        · exact h
        · exfalso
          have hac : a = c := by have := hq.2; simp only at this; omega
          subst hac
          have : b ^ 2 = d ^ 2 := by omega
          have := Nat.pow_left_injective (n := 2) (by norm_num) this
          subst this
          exact hnt1 rfl
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, h3.1, h3.2.1, h4.1, h4.2.1,
        h1.1, h1.2.1, h2.1, h2.2.1, heq.symm, ?_, ?_⟩, hlt⟩
      · have := h1.2.2; have := h2.2.2; have := h3.2.2; have := h4.2.2
        simp only [mem_product, mem_range]
        omega
      · intro h; apply hnt1; simp only [Prod.mk.injEq] at h ⊢; omega
      · intro h; apply hnt; simp only [Prod.mk.injEq] at h ⊢; omega
    · rintro ⟨a, b, c, d⟩ _ ⟨a', b', c', d'⟩ _ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      rfl
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := oddCollisions X) (fun q : ℕ × ℕ × ℕ × ℕ => q.2.2.1 < q.1)
  omega

/-- LEAF: Rieger pages 95 and 96, displays 18 to 20. Class HARD. The parameterized count
is `O(n / log³ n)` at `X = √n`: a sieve upper bound for the four linear forms in `g, h`
for fixed `u, v`, then the average of the singular factors over `u, v`. -/
theorem paramQuads_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ((paramQuads (Nat.sqrt n)).card : ℝ) ≤ K * (n : ℝ) / Real.log n ^ 3 := by
  sorry

/-- The exact statement of `Decomp577d.rieger_nontrivial_collision_bound`, from the three
leaves of this file. -/
theorem rieger_nontrivial_collision_bound_of_leaves :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ n₁ n : ℕ,
      N₀ ≤ n → n ≤ n₁ → collisionCount n₁ n ≤ K * (n : ℝ) / Real.log n ^ 3 := by
  obtain ⟨K, hK, N₀, hN⟩ := paramQuads_bound
  refine ⟨2 * K, by positivity, N₀, fun n₁ n hn _ => ?_⟩
  have h1 := collisionCount_le_oddCollisions n₁ n
  have h2 : ((oddCollisions (Nat.sqrt n)).card : ℝ) ≤
      2 * ((paramQuads (Nat.sqrt n)).card : ℝ) := by
    exact_mod_cast oddCollisions_le_paramQuads (Nat.sqrt n)
  have h3 := hN n hn
  calc collisionCount n₁ n ≤ 2 * ((paramQuads (Nat.sqrt n)).card : ℝ) := h1.trans h2
    _ ≤ 2 * (K * (n : ℝ) / Real.log n ^ 3) := by linarith
    _ = 2 * K * (n : ℝ) / Real.log n ^ 3 := by ring

end LeanLab.Hathi2021.Decomp577dLeavesRieger

