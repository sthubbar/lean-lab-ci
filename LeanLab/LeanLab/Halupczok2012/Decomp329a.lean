import LeanLab.Halupczok2012.Fourier398

/-!
Finite supply for the counting step of Corollary 1.3 on pages 345 to 346.
The exceptional set is evaluated at the translated midpoint.
The endpoint costs at most one candidate.
This theorem assumes a finite surplus and has no analytic input.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Decomp329a

open scoped Classical

set_option maxHeartbeats 1000000 in
/-- Pages 345 to 346, the finite counting proof for any eligible family of first primes.
Eligibility means that the remaining even number is not 2 modulo 6. -/
theorem representation_of_eligible_surplus (S : Finset ℕ) {X1 X2 Y : ℝ} {n : ℕ}
    (hX1 : 3 ≤ X1) (hnonneg : 0 ≤ X2 + Y)
    (hnodd : Odd n) (hsum : X1 + X2 + 2 * Y ≤ n)
    (hSsub : ∀ p ∈ S, p.Prime ∧ X1 < (p : ℝ) ∧ (p : ℝ) ≤ X1 + Y ∧ IsP 2 (p + 2))
    (heligible : ∀ p ∈ S, (n - p) % 6 ≠ 2)
    (hcnt : cor2Exc (((n : ℝ) - X1 - Y) / 2) X2 Y + 2 ≤ S.card) :
    Cor3Sol n X1 X2 Y := by
  set K1 : ℝ := ((n : ℝ) - X1 - Y) / 2 with hK1

  have hpgt3 : ∀ p ∈ S, 3 < p := by
    intro p hp
    have h1 : (3 : ℝ) < (p : ℝ) := by linarith [(hSsub p hp).2.1]
    exact_mod_cast h1
  have hpnn : ∀ p ∈ S, p ≤ n := by
    intro p hp
    have h2 : (p : ℝ) ≤ X1 + Y := (hSsub p hp).2.2.1
    have hX2Y : (0 : ℝ) ≤ X2 + Y := hnonneg
    have : (p : ℝ) ≤ (n : ℝ) := by linarith
    exact_mod_cast this

  -- the map `p ↦ (n - p)/2`
  set tf : ℕ → ℕ := fun p => (n - p) / 2 with htf
  have ht2 : ∀ p ∈ S, 2 * tf p = n - p := by
    intro p hp
    have hpodd : Odd p := (hSsub p hp).1.odd_of_ne_two (by have := hpgt3 p hp; omega)
    have heven : Even (n - p) := Nat.Odd.sub_odd hnodd hpodd
    have hdvd : 2 ∣ n - p := even_iff_two_dvd.mp heven
    have := Nat.div_mul_cancel hdvd
    simp only [htf]
    omega
  have hmod6 : ∀ p ∈ S, (2 * tf p) % 6 ≠ 2 := by
    intro p hp
    rw [ht2 p hp]
    exact heligible p hp

  have htmem : ∀ p ∈ S, (p : ℝ) < X1 + Y → tf p ∈ kRange K1 Y := by
    intro p hp hplt
    have hpgt : X1 < (p : ℝ) := (hSsub p hp).2.1
    have h2t := ht2 p hp
    have hpn : p ≤ n := hpnn p hp
    rw [Fourier398.window_mem]
    have hcast : ((n - p : ℕ) : ℝ) = (n : ℝ) - (p : ℝ) := by
      rw [Nat.cast_sub hpn]
    have ht_eq : ((tf p : ℕ) : ℝ) = ((n : ℝ) - (p : ℝ)) / 2 := by
      have hh : ((2 * tf p : ℕ) : ℝ) = (n : ℝ) - (p : ℝ) := by
        rw [h2t]; exact hcast
      push_cast at hh
      linarith
    constructor <;> rw [ht_eq, hK1] <;> linarith

  -- split `S` into the part below `X1 + Y` (which maps into `kRange K1 Y`) and the rest
  set S' : Finset ℕ := S.filter (fun p => (p : ℝ) < X1 + Y) with hS'def
  set S'' : Finset ℕ := S.filter (fun p => X1 + Y ≤ (p : ℝ)) with hS''def
  have hScover : S ⊆ S' ∪ S'' := by
    intro p hp
    by_cases h : (p : ℝ) < X1 + Y
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, not_lt.mp h⟩)
  have hS''le : S''.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [hS''def, Finset.mem_filter] at ha hb
    have ha2 : (a : ℝ) ≤ X1 + Y := (hSsub a ha.1).2.2.1
    have hb2 : (b : ℝ) ≤ X1 + Y := (hSsub b hb.1).2.2.1
    have : (a : ℝ) = (b : ℝ) := by linarith [ha.2, hb.2]
    exact_mod_cast this
  have hScard : S.card ≤ S'.card + 1 := by
    have h1 : S.card ≤ (S' ∪ S'').card := Finset.card_le_card hScover
    have h2 : (S' ∪ S'').card ≤ S'.card + S''.card := Finset.card_union_le _ _
    omega
  have hinj : Set.InjOn tf ↑S' := by
    intro p hp q hq heq
    have hpS : p ∈ S := (Finset.mem_filter.mp hp).1
    have hqS : q ∈ S := (Finset.mem_filter.mp hq).1
    have h2p := ht2 p hpS
    have h2q := ht2 q hqS
    have hpq : n - p = n - q := by rw [← h2p, ← h2q, heq]
    have := hpnn p hpS
    have := hpnn q hqS
    omega
  have himgcard : (S'.image tf).card = S'.card := Finset.card_image_of_injOn hinj

  -- some Wu prime is not an exception, hence gives the third prime
  set E : Finset ℕ := (kRange K1 Y).filter (fun k => (2 * k) % 6 ≠ 2 ∧
    ¬ ∃ p2 p3 : ℕ, p2.Prime ∧ p3.Prime ∧ p2 + p3 = 2 * k ∧ IsP 3 (p2 + 2) ∧
      X2 < p2 ∧ (p2 : ℝ) ≤ X2 + Y) with hEdef
  have hEcor : E.card = cor2Exc K1 X2 Y := by
    rw [hEdef]
    rfl
  have hnotsub : ¬ (S'.image tf ⊆ E) := by
    intro hsub
    have h1 : (S'.image tf).card ≤ E.card := Finset.card_le_card hsub
    have h2 : E.card = cor2Exc K1 X2 Y := hEcor
    omega
  obtain ⟨k, hkimg, hknot⟩ := Finset.not_subset.mp hnotsub
  obtain ⟨p, hpS', hpk⟩ := Finset.mem_image.mp hkimg
  have hpS : p ∈ S := (Finset.mem_filter.mp hpS').1
  have hplt : (p : ℝ) < X1 + Y := (Finset.mem_filter.mp hpS').2
  have htmem' : tf p ∈ kRange K1 Y := htmem p hpS hplt
  rw [← hpk] at hknot
  have hgood : ¬ ((2 * tf p) % 6 ≠ 2 ∧
      ¬ ∃ p2 p3 : ℕ, p2.Prime ∧ p3.Prime ∧ p2 + p3 = 2 * tf p ∧ IsP 3 (p2 + 2) ∧
        X2 < p2 ∧ (p2 : ℝ) ≤ X2 + Y) := by
    intro hcon
    exact hknot (Finset.mem_filter.mpr ⟨htmem', hcon⟩)
  have hmod' : (2 * tf p) % 6 ≠ 2 := hmod6 p hpS
  have hrep : ∃ p2 p3 : ℕ, p2.Prime ∧ p3.Prime ∧ p2 + p3 = 2 * tf p ∧ IsP 3 (p2 + 2) ∧
      X2 < p2 ∧ (p2 : ℝ) ≤ X2 + Y := by
    by_contra hc'
    exact hgood ⟨hmod', hc'⟩
  obtain ⟨p2, p3, hp2, hp3, hsum23, hisp3, hX2lt, hX2le⟩ := hrep
  have hsum3 : p + p2 + p3 = n := by
    have h2t := ht2 p hpS
    have := hpnn p hpS
    omega
  exact ⟨p, p2, p3, (hSsub p hpS).1, hp2, hp3, hsum3, (hSsub p hpS).2.1, (hSsub p hpS).2.2.1,
    hX2lt, hX2le, (hSsub p hpS).2.2.2, hisp3⟩

set_option maxHeartbeats 1000000 in
/-- Pages 345 to 346, the finite counting step of Corollary 1.3.
Two more candidates than exceptions suffice with the half open window convention. -/
theorem representation_of_surplus {X1 X2 Y : ℝ} {n : ℕ}
    (hX1 : 3 ≤ X1) (hnonneg : 0 ≤ X2 + Y)
    (hnodd : Odd n) (hn6 : n % 6 ≠ 1) (hsum : X1 + X2 + 2 * Y ≤ n)
    (hcnt : cor2Exc (((n : ℝ) - X1 - Y) / 2) X2 Y + 2 ≤
      ((kRange X1 Y).filter (fun p => p.Prime ∧ IsP 2 (p + 2) ∧ ¬ 3 ∣ (p + 2))).card) :
    Cor3Sol n X1 X2 Y := by
  let S : Finset ℕ := (kRange X1 Y).filter
    (fun p => p.Prime ∧ IsP 2 (p + 2) ∧ ¬ 3 ∣ (p + 2))
  have hS : ∀ p ∈ S, p.Prime ∧ X1 < (p : ℝ) ∧ (p : ℝ) ≤ X1 + Y ∧ IsP 2 (p + 2) := by
    intro p hp
    obtain ⟨hkr, hpr, hisp, _⟩ := Finset.mem_filter.mp hp
    obtain ⟨hlo, hhi⟩ := (Fourier398.window_mem _ _ _).mp hkr
    exact ⟨hpr, hlo, hhi, hisp⟩
  apply representation_of_eligible_surplus S hX1 hnonneg hnodd hsum hS ?_ hcnt
  intro p hp
  have hpgt3 : 3 < p := by
    have h : (3 : ℝ) < p := by linarith [(hS p hp).2.1]
    exact_mod_cast h
  have hpn : p ≤ n := by
    have h : (p : ℝ) ≤ n := by linarith [(hS p hp).2.2.1]
    exact_mod_cast h
  have hpodd := (hS p hp).1.odd_of_ne_two (by omega)
  have hp3 : p % 3 ≠ 0 := by
    intro h
    have heq := (Nat.prime_dvd_prime_iff_eq Nat.prime_three (hS p hp).1).mp
      (Nat.dvd_of_mod_eq_zero h)
    omega
  have hp32 : (p + 2) % 3 ≠ 0 := by
    intro h
    exact (Finset.mem_filter.mp hp).2.2.2 (Nat.dvd_of_mod_eq_zero h)
  obtain ⟨a, ha⟩ := hpodd
  obtain ⟨b, hb⟩ := hnodd
  have hp2 : p % 2 = 1 := by omega
  have hpmod3 : p % 3 = 2 := by omega
  have hp62 : (p % 6) % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd _ (by norm_num : 2 ∣ 6)]
    exact hp2
  have hp63 : (p % 6) % 3 = 2 := by
    rw [Nat.mod_mod_of_dvd _ (by norm_num : 3 ∣ 6)]
    exact hpmod3
  have hp6 : p % 6 = 5 := by omega
  have hn6' : n % 6 = 3 ∨ n % 6 = 5 := by omega
  rcases hn6' with h | h <;> omega

/-- Pages 345 to 346, a concrete nonvacuity check for the finite surplus theorem.
The midpoint is 25 over 2 and the candidate primes 11 and 17 suffice. -/
theorem surplus_instance :
    cor2Exc (25 / 2) 10 10 = 0 ∧
      2 ≤ ((kRange 10 10).filter
        (fun p => p.Prime ∧ IsP 2 (p + 2) ∧ ¬ 3 ∣ (p + 2))).card := by
  have h13 : IsP 3 13 := isP_mono (by norm_num) (isP_prime (by norm_num))
  have h19 : IsP 3 19 := isP_mono (by norm_num) (isP_prime (by norm_num))
  constructor
  · unfold cor2Exc
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro k hk hbad
    rcases hbad with ⟨hmod, hbad⟩
    have hkmem := (Fourier398.window_mem _ _ _).mp hk
    have hklo : 13 ≤ k := by
      have : (12 : ℝ) < k := by linarith [hkmem.1]
      have hkn : 12 < k := by exact_mod_cast this
      omega
    have hkhi : k ≤ 22 := by
      have : (k : ℝ) < 23 := by linarith [hkmem.2]
      have hkn : k < 23 := by exact_mod_cast this
      omega
    interval_cases k
    all_goals norm_num at hmod
    · exact hbad ⟨11, 17, by norm_num, by norm_num, by norm_num, h13,
        by norm_num, by norm_num⟩
    · exact hbad ⟨11, 19, by norm_num, by norm_num, by norm_num, h13,
        by norm_num, by norm_num⟩
    · exact hbad ⟨11, 23, by norm_num, by norm_num, by norm_num, h13,
        by norm_num, by norm_num⟩
    · exact hbad ⟨17, 19, by norm_num, by norm_num, by norm_num, h19,
        by norm_num, by norm_num⟩
    · exact hbad ⟨11, 29, by norm_num, by norm_num, by norm_num, h13,
        by norm_num, by norm_num⟩
    · exact hbad ⟨11, 31, by norm_num, by norm_num, by norm_num, h13,
        by norm_num, by norm_num⟩
  · have h13' : IsP 2 13 := isP_mono (by norm_num) (isP_prime (by norm_num))
    have h19' : IsP 2 19 := isP_mono (by norm_num) (isP_prime (by norm_num))
    have hs : ({11, 17} : Finset ℕ) ⊆ (kRange 10 10).filter
        (fun p => p.Prime ∧ IsP 2 (p + 2) ∧ ¬ 3 ∣ (p + 2)) := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨(Fourier398.window_mem _ _ _).mpr
          ⟨by norm_num, by norm_num⟩, by norm_num, h13', by norm_num⟩
      · exact Finset.mem_filter.mpr ⟨(Fourier398.window_mem _ _ _).mpr
          ⟨by norm_num, by norm_num⟩, by norm_num, h19', by norm_num⟩
    simpa using Finset.card_le_card hs

/-- Page 333, an unbounded family satisfying the numerical domain of Corollary 1.3.
Use epsilon one quarter and upper bound constant five. -/
theorem corollary3_domain (m : ℕ) (hm : 1 ≤ m) :
    (3 : ℝ) ≤ 3 * m ∧
    (3 * (m : ℝ)) ^ (0.971 : ℝ) ≤ 3 * m ∧
    (3 * (m : ℝ)) ^ (0.861 : ℝ) ≤ 3 * m ∧
    Odd (12 * m + 3) ∧ (12 * m + 3) % 6 ≠ 1 ∧
    3 * (m : ℝ) + 3 * m + 2 * (3 * m) ≤ (12 * m + 3 : ℕ) ∧
    ((12 * m + 3 : ℕ) : ℝ) ≤ 5 * (3 * (m : ℝ)) ^ (3 / 2 - 1 / 4 : ℝ) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have ht1 : (1 : ℝ) ≤ 3 * m := by linarith
  have hpow1 : (3 * (m : ℝ)) ^ (0.971 : ℝ) ≤ 3 * m := by
    simpa using Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num : (0.971 : ℝ) ≤ 1)
  have hpow2 : (3 * (m : ℝ)) ^ (0.861 : ℝ) ≤ 3 * m := by
    simpa using Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num : (0.861 : ℝ) ≤ 1)
  have hpow3 : 3 * (m : ℝ) ≤ (3 * (m : ℝ)) ^ (3 / 2 - 1 / 4 : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le ht1
      (by norm_num : (1 : ℝ) ≤ 3 / 2 - 1 / 4)
  refine ⟨by linarith, hpow1, hpow2, ⟨6 * m + 1, by omega⟩, by omega, ?_, ?_⟩
  · push_cast
    linarith
  · push_cast
    linarith

end LeanLab.Halupczok2012.Decomp329a
