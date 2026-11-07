/-
Shao Theorem 1.3 with an explicit residue profile and a reusable lifting step.
Source: https://arxiv.org/abs/1206.6139v2 pages 15 to 17.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.DensityGoldbach.Decomp408a
import LeanLab.DensityGoldbach.Profiles408
import LeanLab.DensityGoldbach.U1488Window

open Finset

namespace LeanLab.DensityGoldbach.Decomp408b

section LocalProfileHelpers

set_option maxHeartbeats 2000000

open Filter
open scoped Classical

/-- PNT in progressions at `k = 0`: the class log sum is at most `(1 + ε) x / φ(W)`. -/
theorem theta_class_upper (W : ℕ) (hW : 0 < W) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ r : ℕ, Nat.Coprime r W →
      ∑ p ∈ (range (x + 1)).filter (fun p => p.Prime ∧ p % W = r % W), Real.log p
        ≤ (1 + ε) * (x : ℝ) / (W.totient : ℝ) := by
  have hφ : (0 : ℝ) < (W.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.2 hW
  obtain ⟨n₀, hn₀⟩ := LeanLab.HardyLittlewood1923.ap_sum_pow 0 W (by omega) (ε / (W.totient : ℝ))
    (by positivity)
  refine ⟨n₀, fun x hx r hr => ?_⟩
  have h := hn₀ x hx r hr
  have h2 : ∑ p ∈ (range (x + 1)).filter (fun p => p.Prime ∧ p % W = r % W), Real.log p
      - (x : ℝ) / (W.totient : ℝ) ≤ (ε / (W.totient : ℝ)) * (x : ℝ) := by
    simpa using (abs_le.1 h).2
  have h3 : (1 + ε) * (x : ℝ) / (W.totient : ℝ)
      = (x : ℝ) / (W.totient : ℝ) + (ε / (W.totient : ℝ)) * (x : ℝ) := by
    field_simp
  linarith

section Basics

variable {z m : ℕ}

lemma half_eq (hm : primorial z = 2 * m) : primorial z / 2 = m := by omega

lemma odd_of_w (hz : 3 ≤ z) (hm : primorial z = 2 * m) : Odd m := by
  obtain ⟨-, ho, -, -⟩ := half_primorial_props hz
  rwa [half_eq hm] at ho

lemma three_dvd_m (hz : 3 ≤ z) (hm : primorial z = 2 * m) : 3 ∣ m := by
  obtain ⟨-, -, -, h3⟩ := half_primorial_props hz
  rwa [half_eq hm] at h3

variable [NeZero m]

/-- The odd representative of `b` is an odd residue below `W = z#`, congruent to `b` mod `m`,
and carries the same residue mod `3`. -/
lemma oddRep_props (hz : 3 ≤ z) (hm : primorial z = 2 * m) (b : ZMod m) :
    Profiles408.oddRepresentative m b < primorial z ∧ Odd (Profiles408.oddRepresentative m b) ∧
      Profiles408.oddRepresentative m b % m = b.val ∧
      Profiles408.oddRepresentative m b % 3 = b.val % 3 := by
  obtain ⟨h1, h2, h3⟩ := Profiles408.oddRepresentative_properties m (odd_of_w hz hm) b
  refine ⟨?_, h2, h3, ?_⟩
  · rw [hm]; exact h1
  · have hmod : Nat.ModEq m (Profiles408.oddRepresentative m b) b.val := by
      rw [Nat.ModEq, h3, Nat.mod_eq_of_lt (ZMod.val_lt b)]
    have hmod3 := hmod.of_dvd (three_dvd_m hz hm)
    rw [Nat.ModEq] at hmod3
    exact hmod3

/-- The odd representative of a unit it coprime to `W = z#`. -/
lemma oddRep_coprime (hz : 3 ≤ z) (hm : primorial z = 2 * m) (b : ZMod m) (hb : IsUnit b) :
    Nat.Coprime (Profiles408.oddRepresentative m b) (primorial z) := by
  obtain ⟨-, hodd, hmod, -⟩ := oddRep_props hz hm b
  have hbv : Nat.Coprime b.val m := by
    rw [← ZMod.natCast_zmod_val b] at hb
    exact (ZMod.isUnit_iff_coprime b.val m).mp hb
  have hrm : Nat.Coprime (Profiles408.oddRepresentative m b) m := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hmod]
    exact hbv.gcd_eq_one
  rw [hm, Nat.mul_comm]
  exact hrm.mul_right (Nat.coprime_two_left.mpr hodd).symm

end Basics

section Upper

variable {z m : ℕ} [NeZero m]

/-- A prime in a residue class not coprime to `W = z#` divides `W`, so it is at most `z`. -/
lemma prime_le_of_modEq {z W r p : ℕ} (hW : W = primorial z) (hp : p.Prime)
    (hmod : p % W = r % W) (hr : ¬ Nat.Coprime r W) : p ≤ z := by
  have hg : Nat.gcd r W ≠ 1 := by
    intro h
    exact hr (by rw [Nat.Coprime]; exact h)
  obtain ⟨q, hq, hqg⟩ := Nat.exists_prime_and_dvd hg
  have hqW : q ∣ W := hqg.trans (Nat.gcd_dvd_right r W)
  have hqr : q ∣ r := hqg.trans (Nat.gcd_dvd_left r W)
  have hqle : q ≤ z := by
    rw [hW] at hqW
    exact (Nat.Prime.dvd_primorial_iff hq).mp hqW
  have hmodq : p % q = r % q := by
    have h1 : Nat.ModEq W p r := hmod
    have h2 := Nat.ModEq.of_dvd hqW h1
    exact h2
  have hpqq : q ∣ p := by
    rw [Nat.dvd_iff_mod_eq_zero, hmodq, Nat.dvd_iff_mod_eq_zero.mp hqr]
  have hqp : q = p := by
    rcases (Nat.dvd_prime hp).mp hpqq with h | h
    · exact absurd h hq.ne_one
    · exact h
  omega


/-- The profile is capped by `1`. -/
theorem profile_le_one (A : Set ℕ) (hA : A ⊆ P) (hz : 3 ≤ z) (hm : primorial z = 2 * m)
    (δ : ℝ) (hδ : 0 < δ) (hδ8 : δ ≤ 1 / 8) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ b : ZMod m,
      Profiles408.halfProfile A z n δ m b ≤ 1 := by
  have hW : 0 < primorial z := primorial_pos z
  have hφ0 : (0 : ℝ) < ((primorial z).totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.2 hW
  obtain ⟨X₀, hX₀⟩ := theta_class_upper (primorial z) hW (δ / 16) (by positivity)
  refine ⟨max (3 * X₀ + 3)
    (Nat.ceil (3 * ((primorial z).totient : ℝ) * ((z : ℝ) + 1) * Real.log z) + 3),
    fun n hn b => ?_⟩
  have hnX : X₀ ≤ n := by
    have h : 3 * X₀ + 3 ≤ n := le_trans (le_max_left _ _) hn
    omega
  have hn1 : 0 < n := by omega
  have hceil : 3 * ((primorial z).totient : ℝ) * ((z : ℝ) + 1) * Real.log z ≤ (n : ℝ) := by
    have h1 : Nat.ceil (3 * ((primorial z).totient : ℝ) * ((z : ℝ) + 1) * Real.log z) ≤ n := by
      have h := le_trans (le_max_right _ _) hn
      omega
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast h1)
  set x := (2 * n - 1) / 3 with hxdef
  have hxX : X₀ ≤ x := by omega
  have hxle : 3 * x ≤ 2 * n := by omega
  set r := Profiles408.oddRepresentative m b with hrdef
  set T := (range (n + 1)).filter
      (fun p => p ∈ A ∧ p % primorial z = r % primorial z ∧ 3 * p < 2 * n) with hTdef
  set Θ := ∑ p ∈ T, Real.log p with hΘdef
  have hΘle : Θ ≤ (1 + δ / 16) * (x : ℝ) / ((primorial z).totient : ℝ) := by
    by_cases hcop : Nat.Coprime r (primorial z)
    · refine le_trans ?_ (hX₀ x hxX r hcop)
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => Real.log_natCast_nonneg i)
      intro p hp
      rw [hTdef, Finset.mem_filter] at hp
      rw [Finset.mem_filter]
      obtain ⟨hp1, hpA, hpr, hp3⟩ := hp
      exact ⟨by rw [Finset.mem_range] at hp1 ⊢; omega, hA hpA, hpr⟩
    · have hsmall : ∀ p ∈ T, p ≤ z := by
        intro p hp
        rw [hTdef, Finset.mem_filter] at hp
        obtain ⟨-, hpA, hpr, -⟩ := hp
        exact prime_le_of_modEq rfl (hA hpA) hpr hcop
      have hcard : T.card ≤ z + 1 := by
        calc T.card ≤ (range (z + 1)).card := by
              refine Finset.card_le_card ?_
              intro p hp
              exact Finset.mem_range.2 (by have := hsmall p hp; omega)
          _ = z + 1 := Finset.card_range _
      have hlog0 : (0 : ℝ) ≤ Real.log z := Real.log_natCast_nonneg z
      have hΘz : Θ ≤ ((z : ℝ) + 1) * Real.log z := by
        have hs : ∑ _p ∈ T, Real.log z = (T.card : ℝ) * Real.log z := by
          rw [Finset.sum_const, nsmul_eq_mul]
        calc Θ ≤ ∑ _p ∈ T, Real.log z := by
              refine Finset.sum_le_sum fun p hp => ?_
              refine Real.log_le_log (by exact_mod_cast (hA (by
                rw [hTdef, Finset.mem_filter] at hp; exact hp.2.1)).pos) ?_
              exact_mod_cast hsmall p hp
          _ = (T.card : ℝ) * Real.log z := hs
          _ ≤ ((z : ℝ) + 1) * Real.log z := by
              have h1 : (T.card : ℝ) ≤ (z : ℝ) + 1 := by exact_mod_cast hcard
              exact mul_le_mul_of_nonneg_right h1 hlog0
      have hφz : (0:ℝ) ≤ ((primorial z).totient : ℝ) * ((z : ℝ) + 1) * Real.log z := by
        have h1 : (0:ℝ) ≤ ((primorial z).totient : ℝ) := hφ0.le
        have h2 : (0:ℝ) ≤ (z : ℝ) + 1 := by positivity
        exact mul_nonneg (mul_nonneg h1 h2) hlog0
      have htwo : 3 * ((primorial z).totient : ℝ) * ((z : ℝ) + 1) * Real.log z
          ≤ 2 * (n : ℝ) := by linarith
      have hkey : 3 * ((primorial z).totient : ℝ) / (2 * n) * Θ ≤ 1 := by
        have h3φ : (0:ℝ) ≤ 3 * ((primorial z).totient : ℝ) := by positivity
        have h1 : 3 * ((primorial z).totient : ℝ) * Θ
            ≤ 3 * ((primorial z).totient : ℝ) * (((z : ℝ) + 1) * Real.log z) :=
          mul_le_mul_of_nonneg_left hΘz h3φ
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < 2 * n)]
        linarith
      have hxlb : 2 * n ≤ 3 * x + 3 := by omega
      have hx2 : (1:ℝ) ≤ (x : ℝ) := by
        have h2n : 4 ≤ 2 * n := by omega
        have : 1 ≤ x := by omega
        exact_mod_cast this
      calc Θ ≤ ((z : ℝ) + 1) * Real.log z := hΘz
        _ ≤ (1 + δ / 16) * (x : ℝ) / ((primorial z).totient : ℝ) := by
            have hx0 : (0:ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
            rw [le_div_iff₀ hφ0]
            have hxlb' : 2 * (n : ℝ) ≤ 3 * (x : ℝ) + 3 := by exact_mod_cast hxlb
            nlinarith [hceil, hxlb', hx2, hx0, hδ]
  have hnorm : (0 : ℝ) ≤ 3 * ((primorial z).totient : ℝ) / (2 * n) := by positivity
  have hfin : 3 * ((primorial z).totient : ℝ) / (2 * n) * Θ ≤ 1 + δ / 16 := by
    refine le_trans (mul_le_mul_of_nonneg_left hΘle hnorm) ?_
    have e : 3 * ((primorial z).totient : ℝ) / (2 * n) *
        ((1 + δ / 16) * (x : ℝ) / ((primorial z).totient : ℝ))
        = (1 + δ / 16) * (3 * (x : ℝ) / (2 * (n : ℝ))) := by
      field_simp
    rw [e]
    have hxle' : 3 * (x : ℝ) / (2 * (n : ℝ)) ≤ 1 := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * (n : ℝ))]
      have : 3 * (x : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hxle
      linarith
    have hpos : (0:ℝ) ≤ 1 + δ / 16 := by linarith
    nlinarith
  rw [Profiles408.halfProfile, Profiles408.primeProfile, ← hrdef, ← hΘdef]
  refine max_le ?_ zero_le_one
  have h16 : δ / 16 ≤ δ / 8 := by linarith
  linarith

end Upper

section Pos

variable {z m : ℕ} [NeZero m]

/-- Every reduced class has positive profile for large `n`: the lower density `δ` in each
class gives a class log sum at least `δ x / (4 φ(W))`, which beats the shift `δ/8`. -/
theorem profile_pos_eventually (A : Set ℕ) (hA : A ⊆ P) (hz : 3 ≤ z) (hm : primorial z = 2 * m)
    (δ : ℝ) (hδ : 0 < δ)
    (hlocal : ∀ b, b < primorial z → Nat.Coprime b (primorial z) →
      δ ≤ lowerDensityRes A b (primorial z)) :
    ∀ᶠ n : ℕ in atTop, ∀ b : ZMod m, IsUnit b →
      0 < Profiles408.halfProfile A z n δ m b := by
  have hW : 0 < primorial z := primorial_pos z
  have hφ0 : (0 : ℝ) < ((primorial z).totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.2 hW
  suffices h : ∀ᶠ n : ℕ in atTop, ∀ b ∈ (Finset.univ : Finset (ZMod m)), IsUnit b →
      0 < Profiles408.halfProfile A z n δ m b by simpa using h
  rw [Filter.eventually_all_finset]
  intro b _
  by_cases hb : IsUnit b
  · set r := Profiles408.oddRepresentative m b with hrdef
    obtain ⟨hlt, -, -, -⟩ := oddRep_props hz hm b
    have hcop : Nat.Coprime r (primorial z) := oddRep_coprime hz hm b hb
    have hd : δ / 2 < lowerDensityRes A r (primorial z) := by
      have := hlocal r hlt hcop
      linarith
    obtain ⟨Xr, hXr⟩ := LeanLab.DensityGoldbach.U1446.theta_A_lower A hA (primorial z) r hW hcop (δ / 2) (by positivity)
      hd (1 / 2) (by norm_num) (by norm_num)
    refine Filter.Eventually.mono (Filter.eventually_ge_atTop (max (3 * Xr + 3) 4)) ?_
    intro n hn _
    have hn3 : 3 * Xr + 3 ≤ n := le_trans (le_max_left _ _) hn
    have hn4 : 4 ≤ n := le_trans (le_max_right _ _) hn
    set x := (2 * n - 1) / 3 with hxdef
    have hn1 : 0 < n := by omega
    have hxX : Xr ≤ x := by omega
    have hxle : 3 * x ≤ 2 * n := by omega
    have hxs : 3 * x ≤ 2 * n - 1 := by omega
    have hxn : x ≤ n := by omega
    have h3xn : n < 3 * x := by omega
    set T := (range (n + 1)).filter
      (fun p => p ∈ A ∧ p % primorial z = r % primorial z ∧ 3 * p < 2 * n) with hTdef
    have hTheta : ∑ p ∈ (range (x + 1)).filter
          (fun p => p ∈ A ∧ p.Prime ∧ p % primorial z = r % primorial z), Real.log p
        ≤ ∑ p ∈ T, Real.log p := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => Real.log_natCast_nonneg i)
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hp1, hpA, hpp, hpr⟩ := hp
      rw [Finset.mem_range] at hp1
      rw [hTdef, Finset.mem_filter]
      have hpx : p ≤ x := by omega
      refine ⟨?_, hpA, hpr, ?_⟩
      · rw [Finset.mem_range]; omega
      · have h3 : 3 * p ≤ 3 * x := Nat.mul_le_mul_left 3 hpx
        omega
    have hstep := hXr x hxX
    have hlow : δ * (x : ℝ) / (4 * ((primorial z).totient : ℝ)) ≤ ∑ p ∈ T, Real.log p := by
      have h2 : δ / 2 * (1 - 1 / 2) * (x : ℝ) / ((primorial z).totient : ℝ)
          = δ * (x : ℝ) / (4 * ((primorial z).totient : ℝ)) := by
        field_simp
        ring
      rw [h2] at hstep
      exact le_trans hstep hTheta
    have hc : (0:ℝ) ≤ 3 * ((primorial z).totient : ℝ) / (2 * n) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hlow hc
    have he : 3 * ((primorial z).totient : ℝ) / (2 * n) *
        (δ * (x : ℝ) / (4 * ((primorial z).totient : ℝ))) = 3 * δ * (x : ℝ) / (8 * (n : ℝ)) := by
      field_simp
      ring
    have hposmain : 3 * δ * (x : ℝ) / (8 * (n : ℝ)) - δ / 8 > 0 := by
      have h3xn' : (n : ℝ) < 3 * (x : ℝ) := by exact_mod_cast h3xn
      have hnum : 3 * δ * (x : ℝ) - δ * (n : ℝ) > 0 := by nlinarith
      have e2 : 3 * δ * (x : ℝ) / (8 * (n : ℝ)) - δ / 8
          = (3 * δ * (x : ℝ) - δ * (n : ℝ)) / (8 * (n : ℝ)) := by
        field_simp
      rw [e2]
      exact div_pos hnum (by positivity)
    rw [Profiles408.halfProfile, Profiles408.primeProfile, ← hrdef, ← hTdef]
    refine lt_of_lt_of_le ?_ (le_max_left (3 * ((primorial z).totient : ℝ) / (2 * ↑n)
      * (∑ p ∈ T, Real.log ↑p) - δ / 8) 0)
    rw [he] at hmul
    linarith
  · exact Filter.Eventually.of_forall (fun n h => absurd h hb)

end Pos

set_option maxHeartbeats 2000000

section Alpha

variable {z m : ℕ} [NeZero m]

/-- The odd representative is determined by being odd, below `2m`, and congruent to `b`. -/
lemma oddRep_eq_of (hz : 3 ≤ z) (hm : primorial z = 2 * m) (b : ZMod m) (r : ℕ)
    (hodd : Odd r) (hlt : r < 2 * m) (hmod : r % m = b.val) :
    Profiles408.oddRepresentative m b = r := by
  obtain ⟨h1, h2, h3, -⟩ := oddRep_props hz hm b
  have h1' : Profiles408.oddRepresentative m b < 2 * m := by
    rw [hm] at h1; exact h1
  have hmodd : Odd m := odd_of_w hz hm
  have e1 : Nat.ModEq m (Profiles408.oddRepresentative m b) r := by
    rw [Nat.ModEq, h3, hmod]
  have e2 : Nat.ModEq 2 (Profiles408.oddRepresentative m b) r := by
    rw [Nat.ModEq, Nat.odd_iff.mp h2, Nat.odd_iff.mp hodd]
  have e3 : Nat.ModEq (2 * m) (Profiles408.oddRepresentative m b) r :=
    (Nat.modEq_and_modEq_iff_modEq_mul (Nat.coprime_two_left.mpr hmodd)).mp ⟨e2, e1⟩
  rw [Nat.ModEq] at e3
  rw [Nat.mod_eq_of_lt h1', Nat.mod_eq_of_lt hlt] at e3
  exact e3

/-- Sums over the reduced classes mod `m` in one residue class mod `3` are sums over the
odd reduced residues below `z#` in that class. -/
theorem sum_unit_class (A : Set ℕ) (hz : 3 ≤ z) (hm : primorial z = 2 * m) (n : ℕ) (δ : ℝ)
    (u : ℕ) :
    ∑ b ∈ (unitsMod m).filter (fun b => b.val % 3 = u % 3),
        Profiles408.halfProfile A z n δ m b
      = ∑ r ∈ (range (primorial z)).filter
          (fun r => Odd r ∧ Nat.Coprime r (primorial z) ∧ r % 3 = u % 3),
        Profiles408.primeProfile A (primorial z) n δ r := by
  have hmW : m ∣ primorial z := by rw [hm]; exact ⟨2, by ring⟩
  have h3m : 3 ∣ m := three_dvd_m hz hm
  refine Finset.sum_bij' (fun b _ => Profiles408.oddRepresentative m b)
    (fun r _ => (r : ZMod m)) ?_ ?_ ?_ ?_ ?_
  · intro b hb
    rw [Finset.mem_filter] at hb
    obtain ⟨hb1, hb3⟩ := hb
    have hunit : IsUnit b := by
      simp only [unitsMod, Finset.mem_filter, Finset.mem_univ, true_and] at hb1
      exact hb1
    obtain ⟨hlt, hodd, hmod, hmod3⟩ := oddRep_props hz hm b
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_range.2 hlt, hodd, oddRep_coprime hz hm b hunit, by rw [hmod3, hb3]⟩
  · intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨hr1, hrodd, hrcop, hr3⟩ := hr
    have hrm : Nat.Coprime r m := hrcop.of_dvd_right hmW
    have hrt : r < 2 * m := by
      rw [Finset.mem_range] at hr1
      rw [hm] at hr1; exact hr1
    rw [Finset.mem_filter]
    constructor
    · simp only [unitsMod, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (ZMod.isUnit_iff_coprime r m).mpr hrm
    · rw [ZMod.val_natCast m r]
      have h : (r % m) % 3 = r % 3 := Nat.mod_mod_of_dvd r h3m
      rw [h, hr3]
  · intro b hb
    obtain ⟨-, -, hmod, -⟩ := oddRep_props hz hm b
    have h : ((Profiles408.oddRepresentative m b : ℕ) : ZMod m) = b := by
      conv_rhs => rw [← ZMod.natCast_zmod_val b]
      rw [ZMod.natCast_eq_natCast_iff, Nat.ModEq, hmod, Nat.mod_eq_of_lt (ZMod.val_lt b)]
    exact h
  · intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨hr1, hrodd, hrcop, hr3⟩ := hr
    refine oddRep_eq_of hz hm _ r hrodd ?_ ?_
    · rw [Finset.mem_range] at hr1; rw [hm] at hr1; exact hr1
    · exact (ZMod.val_natCast m r).symm
  · intro b hb
    rfl


/-- The odd representative of a reduced class is an odd reduced residue below `z#`. -/
lemma oddRep_mem (hz : 3 ≤ z) (hm : primorial z = 2 * m) (u : ℕ) {b : ZMod m}
    (hb : b ∈ (unitsMod m).filter (fun b => b.val % 3 = u % 3)) :
    Profiles408.oddRepresentative m b ∈ (range (primorial z)).filter
      (fun r => Odd r ∧ Nat.Coprime r (primorial z) ∧ r % 3 = u % 3) := by
  rw [Finset.mem_filter] at hb
  obtain ⟨hb1, hb3⟩ := hb
  have hunit : IsUnit b := by
    simp only [unitsMod, Finset.mem_filter, Finset.mem_univ, true_and] at hb1
    exact hb1
  obtain ⟨hlt, hodd, hmod, hmod3⟩ := oddRep_props hz hm b
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_range.2 hlt, hodd, oddRep_coprime hz hm b hunit, by rw [hmod3, hb3]⟩

/-- The cast of an odd reduced residue below `z#` is a reduced class in the same class mod 3. -/
lemma cast_mem (hz : 3 ≤ z) (hm : primorial z = 2 * m) (u : ℕ) {r : ℕ}
    (hr : r ∈ (range (primorial z)).filter
      (fun r => Odd r ∧ Nat.Coprime r (primorial z) ∧ r % 3 = u % 3)) :
    (r : ZMod m) ∈ (unitsMod m).filter (fun b => b.val % 3 = u % 3) := by
  rw [Finset.mem_filter] at hr
  obtain ⟨hr1, hrodd, hrcop, hr3⟩ := hr
  have hmW : m ∣ primorial z := by rw [hm]; exact ⟨2, by ring⟩
  have h3m : 3 ∣ m := three_dvd_m hz hm
  have hrm : Nat.Coprime r m := hrcop.of_dvd_right hmW
  rw [Finset.mem_filter]
  constructor
  · simp only [unitsMod, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (ZMod.isUnit_iff_coprime r m).mpr hrm
  · rw [ZMod.val_natCast m r]
    have h : (r % m) % 3 = r % 3 := Nat.mod_mod_of_dvd r h3m
    rw [h, hr3]

/-- The odd representative is injective on `ZMod m`. -/
lemma oddRep_inj (hz : 3 ≤ z) (hm : primorial z = 2 * m) {b₁ b₂ : ZMod m}
    (h : Profiles408.oddRepresentative m b₁ = Profiles408.oddRepresentative m b₂) : b₁ = b₂ := by
  have h1 := (oddRep_props hz hm b₁).2.2.1
  have h2 := (oddRep_props hz hm b₂).2.2.1
  rw [h] at h1
  have hv : b₁.val = b₂.val := by rw [← h1, h2]
  exact ZMod.val_injective m hv

/-- The class fibres mod `m` and below `z#` have the same size. -/
lemma card_class_eq (hz : 3 ≤ z) (hm : primorial z = 2 * m) (u : ℕ) :
    #((unitsMod m).filter (fun b => b.val % 3 = u % 3))
      = #((range (primorial z)).filter
          (fun r => Odd r ∧ Nat.Coprime r (primorial z) ∧ r % 3 = u % 3)) := by
  refine Finset.card_bij (fun b _ => Profiles408.oddRepresentative m b)
    (fun b hb => oddRep_mem hz hm u hb) ?_ ?_
  · intro b₁ hb₁ b₂ hb₂ h
    exact oddRep_inj hz hm h
  · intro r hr
    refine ⟨(r : ZMod m), cast_mem hz hm u hr, oddRep_eq_of hz hm _ r
      (Finset.mem_filter.1 hr).2.1 ?_ (ZMod.val_natCast m r).symm⟩
    have h := (Finset.mem_filter.1 hr).1
    rw [Finset.mem_range] at h
    rw [hm] at h
    exact h


/-- Each class mod `3` holds exactly half of the reduced residues mod `m`, i.e. `φ(z#)/2`. -/
lemma card_class (hz : 3 ≤ z) (hm : primorial z = 2 * m) (u : ℕ) (hu : u % 3 ≠ 0) :
    #((unitsMod m).filter (fun b => b.val % 3 = u % 3)) = (primorial z).totient / 2 := by
  have h3m : 3 ∣ m := three_dvd_m hz hm
  obtain ⟨hpos, hodd0, hsq0, -⟩ := half_primorial_props hz
  have hmpos : primorial z / 2 = m := half_eq hm
  have hoddm : Odd m := by rw [← hmpos]; exact hodd0
  have hsq : Squarefree m := by rw [← hmpos]; exact hsq0
  obtain ⟨k, hmk⟩ : ∃ k, m = 3 * k := ⟨m / 3, by
    have h := Nat.div_mul_cancel h3m
    omega⟩
  subst hmk
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, mul_zero] at hm; exact absurd hm (primorial_pos z).ne'
    · exact h
  have hoddk : Odd k := by
    have h : Odd (3 * k) := hoddm
    rcases Nat.even_or_odd k with he | ho
    · exfalso
      obtain ⟨j, hj⟩ := he
      rw [hj] at h
      obtain ⟨t, ht⟩ := h
      omega
    · exact ho
  have hnk : ¬ 3 ∣ k := by
    rintro ⟨j, hj⟩
    have hdvd : 3 * 3 ∣ 3 * k := by
      refine ⟨j, ?_⟩
      rw [hj]; ring
    have hunit := hsq 3 hdvd
    have h31 : 3 = 1 := Nat.isUnit_iff.mp hunit
    omega
  have hk3 : Nat.Coprime 3 k := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hnk
  have hiu : ((u : ℕ) : ZMod 3) ≠ 0 := by
    intro h
    apply hu
    have h2 : ((u : ℕ) : ZMod 3) = ((0 : ℕ) : ZMod 3) := by simpa using h
    have h3 : u ≡ 0 [MOD 3] := (ZMod.natCast_eq_natCast_iff u 0 3).mp h2
    rw [Nat.ModEq] at h3
    simpa using h3
  haveI : NeZero k := ⟨by omega⟩
  have hfil : (unitsMod (3 * k)).filter (fun b => b.val % 3 = u % 3)
      = (unitsMod (3 * k)).filter (fun b => ((b.val : ℕ) : ZMod 3) = ((u : ℕ) : ZMod 3)) := by
    refine Finset.filter_congr ?_
    intro b _
    rw [ZMod.natCast_eq_natCast_iff, Nat.ModEq]
  have hcardk : #(unitsMod k) = k.totient := by
    rw [unitsMod, ← ZMod.card_units_eq_totient, ← Fintype.card_coe]
    exact Fintype.card_congr
      { toFun := fun u => IsUnit.unit (Finset.mem_filter.1 u.2).2
        invFun := fun u => ⟨(u : ZMod k), Finset.mem_filter.2 ⟨Finset.mem_univ _, u.isUnit⟩⟩
        left_inv := fun u => by simp
        right_inv := fun u => by ext; simp }
  have hfiberN : #((unitsMod (3 * k)).filter
      (fun b => ((b.val : ℕ) : ZMod 3) = ((u : ℕ) : ZMod 3))) = k.totient := by
    have hf := sum_fiber3 hk3 (fun _ => (1 : ℝ)) ((u : ℕ) : ZMod 3) hiu
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hf
    rw [hcardk] at hf
    exact_mod_cast hf
  rw [hfil, hfiberN]
  have hφ : (primorial z).totient = 2 * k.totient := by
    have hc1 : Nat.Coprime 2 (3 * k) := by
      rw [Nat.coprime_comm, Nat.coprime_mul_iff_left]
      exact ⟨by norm_num, (Nat.coprime_comm).mpr (Nat.coprime_two_left.mpr hoddk)⟩
    calc (primorial z).totient = (2 * (3 * k)).totient := by rw [hm]
      _ = (2 : ℕ).totient * (3 * k).totient := Nat.totient_mul hc1
      _ = (3 * k).totient := by rw [show Nat.totient 2 = 1 from by decide]; ring
      _ = (3 : ℕ).totient * k.totient := Nat.totient_mul hk3
      _ = 2 * k.totient := by rw [show Nat.totient 3 = 2 from by decide]
  rw [hφ]
  omega


/-- `lowerDensityRes` is at most `1`. -/
lemma lowerDensityRes_le_one (A : Set ℕ) (u W : ℕ) : lowerDensityRes A u W ≤ 1 := by
  have hbdd : Filter.IsBoundedUnder (fun x y : ℝ => y ≤ x) Filter.atTop
      (fun N : ℕ => (#{n ∈ Icc 1 N | n ∈ A ∧ n.Prime ∧ n % W = u % W} : ℝ) /
        #{n ∈ Icc 1 N | n.Prime ∧ n % W = u % W}) :=
    Filter.isBoundedUnder_of ⟨0, fun N => by positivity⟩
  refine Filter.liminf_le_of_frequently_le ?_ hbdd
  refine Filter.Frequently.of_forall (fun N => ?_)
  have hsub : (Icc 1 N).filter (fun n => n ∈ A ∧ n.Prime ∧ n % W = u % W)
      ⊆ (Icc 1 N).filter (fun n => n.Prime ∧ n % W = u % W) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    exact ⟨hn.1, hn.2.2.1, hn.2.2.2⟩
  have hcard : (#{n ∈ Icc 1 N | n ∈ A ∧ n.Prime ∧ n % W = u % W} : ℝ)
      ≤ (#{n ∈ Icc 1 N | n.Prime ∧ n % W = u % W} : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  rcases Nat.eq_zero_or_pos (#{n ∈ Icc 1 N | n.Prime ∧ n % W = u % W}) with h | h
  · rw [h]; simp
  · rw [div_le_one (by exact_mod_cast h)]
    exact hcard

/-- A positive integer coprime to `3` is coprime to `3`. -/
lemma coprime_three (u : ℕ) (hu : u % 3 ≠ 0) : Nat.Coprime u 3 := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (by norm_num)]
  intro h
  exact hu (Nat.dvd_iff_mod_eq_zero.mp h)


/-- Regrouping a sum over the odd reduced residues below `z#` into a sum over the `log p`. -/
lemma sum_R_Theta_eq (A : Set ℕ) (z n u : ℕ) :
    ∑ r ∈ (range (primorial z)).filter
        (fun r => Odd r ∧ Nat.Coprime r (primorial z) ∧ r % 3 = u % 3),
        (∑ p ∈ (range (n + 1)).filter
          (fun p => p ∈ A ∧ p % primorial z = r % primorial z ∧ 3 * p < 2 * n), Real.log p)
      = ∑ p ∈ ((range (n + 1)).filter (fun p => p ∈ A ∧ 3 * p < 2 * n)).filter
          (fun p => p % primorial z ∈ (range (primorial z)).filter
            (fun r => Odd r ∧ Nat.Coprime r (primorial z) ∧ r % 3 = u % 3)), Real.log p := by
  have hstep : ∀ r : ℕ,
      (∑ p ∈ (range (n + 1)).filter
          (fun p => p ∈ A ∧ p % primorial z = r % primorial z ∧ 3 * p < 2 * n), Real.log p)
        = ∑ p ∈ (range (n + 1)).filter (fun p => p ∈ A ∧ 3 * p < 2 * n),
            (if p % primorial z = r % primorial z then Real.log p else 0) := by
    intro r
    have hfin : ((range (n + 1)).filter (fun p => p ∈ A ∧ 3 * p < 2 * n)).filter
        (fun p => p % primorial z = r % primorial z)
        = (range (n + 1)).filter
          (fun p => p ∈ A ∧ p % primorial z = r % primorial z ∧ 3 * p < 2 * n) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_range]
      tauto
    rw [← Finset.sum_filter, hfin]
  rw [Finset.sum_congr rfl (fun r _ => hstep r), Finset.sum_comm]
  conv_rhs => rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  have hcongr : ∀ r ∈ (range (primorial z)).filter
      (fun r => Odd r ∧ Nat.Coprime r (primorial z) ∧ r % 3 = u % 3),
      (if p % primorial z = r % primorial z then Real.log p else 0)
        = (if p % primorial z = r then Real.log p else 0) := by
    intro r hr
    have hlt : r < primorial z := Finset.mem_range.1 (Finset.mem_filter.1 hr).1
    rw [Nat.mod_eq_of_lt hlt]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq]


/-- The class log sum below `z#` controls the mod-`3` class log sum. -/
lemma S_lower (A : Set ℕ) (hA : A ⊆ P) (hz : 3 ≤ z) (n u x : ℕ)
    (hx : 3 * x < 2 * n) (hxn : x ≤ n) :
    (∑ p ∈ (range (x + 1)).filter (fun p => p ∈ A ∧ p.Prime ∧ p % 3 = u % 3), Real.log p)
      ≤ (∑ r ∈ (range (primorial z)).filter
            (fun r => Odd r ∧ Nat.Coprime r (primorial z) ∧ r % 3 = u % 3),
          (∑ p ∈ (range (n + 1)).filter
            (fun p => p ∈ A ∧ p % primorial z = r % primorial z ∧ 3 * p < 2 * n), Real.log p))
        + (∑ p ∈ (range (z + 1)).filter Nat.Prime, Real.log p) := by
  rw [sum_R_Theta_eq]
  have h3W : 3 ∣ primorial z := prime_dvd_primorial Nat.prime_three hz
  have hW : 0 < primorial z := primorial_pos z
  have hW2 : 2 ∣ primorial z := prime_dvd_primorial Nat.prime_two (by omega)
  have hsub : (range (x + 1)).filter (fun p => p ∈ A ∧ p.Prime ∧ p % 3 = u % 3)
      ⊆ (((range (n + 1)).filter (fun p => p ∈ A ∧ 3 * p < 2 * n)).filter
          (fun p => p % primorial z ∈ (range (primorial z)).filter
            (fun r => Odd r ∧ Nat.Coprime r (primorial z) ∧ r % 3 = u % 3)))
        ∪ (range (z + 1)).filter Nat.Prime := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hp1, hpA, hpp, hp3⟩ := hp
    rw [Finset.mem_range] at hp1
    have hpz : p.Prime := hA hpA
    rw [Finset.mem_union]
    by_cases hle : p ≤ z
    · right
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hpz⟩
    · left
      refine Finset.mem_filter.2 ⟨Finset.mem_filter.2
        ⟨Finset.mem_range.2 (by omega), hpA, by omega⟩, ?_⟩
      have hlt : p % primorial z < primorial z := Nat.mod_lt _ hW
      have hpn : ¬ p ∣ primorial z := by
        intro hd
        exact absurd ((Nat.Prime.dvd_primorial_iff hpz).mp hd) (by omega)
      have hcop : Nat.Coprime p (primorial z) := (Nat.Prime.coprime_iff_not_dvd hpz).mpr hpn
      have hpodd : Odd (p % primorial z) := by
        have hoddp : Odd p := by
          rcases hpz.eq_two_or_odd with h2 | ho
          · omega
          · exact Nat.odd_iff.mpr ho
        rw [Nat.odd_iff]
        rw [Nat.mod_mod_of_dvd p hW2, Nat.odd_iff.mp hoddp]
      have hcopmod : Nat.Coprime (p % primorial z) (primorial z) := by
        have key : (p % primorial z).gcd (primorial z) ∣ p := by
          have h1 : (p % primorial z).gcd (primorial z) ∣ p % primorial z := Nat.gcd_dvd_left _ _
          have h2 : (p % primorial z).gcd (primorial z) ∣ primorial z := Nat.gcd_dvd_right _ _
          have hsum : p / primorial z * primorial z + p % primorial z = p := by
            rw [mul_comm]
            exact Nat.div_add_mod p (primorial z)
          have := dvd_add (dvd_mul_of_dvd_right h2 (p / primorial z)) h1
          rwa [hsum] at this
        have hdvd1 : (p % primorial z).gcd (primorial z) ∣ 1 := by
          rw [← hcop.gcd_eq_one]
          exact Nat.dvd_gcd key (Nat.gcd_dvd_right _ _)
        rw [Nat.Coprime, Nat.dvd_one.mp hdvd1]
      refine Finset.mem_filter.2 ⟨Finset.mem_range.2 hlt, hpodd, hcopmod, ?_⟩
      have heq : (p % primorial z) % 3 = p % 3 := Nat.mod_mod_of_dvd p h3W
      rw [heq, hp3]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun i _ _ => Real.log_natCast_nonneg i)) ?_
  have hunion : (((range (n + 1)).filter (fun p => p ∈ A ∧ 3 * p < 2 * n)).filter
        (fun p => p % primorial z ∈ (range (primorial z)).filter
          (fun r => Odd r ∧ Nat.Coprime r (primorial z) ∧ r % 3 = u % 3)))
      ∪ (range (z + 1)).filter Nat.Prime
      = (((range (n + 1)).filter (fun p => p ∈ A ∧ 3 * p < 2 * n)).filter
        (fun p => p % primorial z ∈ (range (primorial z)).filter
          (fun r => Odd r ∧ Nat.Coprime r (primorial z) ∧ r % 3 = u % 3)))
      ∪ ((range (z + 1)).filter Nat.Prime \ ((range (n + 1)).filter (fun p => p ∈ A ∧ 3 * p < 2 * n)).filter
        (fun p => p % primorial z ∈ (range (primorial z)).filter
          (fun r => Odd r ∧ Nat.Coprime r (primorial z) ∧ r % 3 = u % 3))) := by
    ext p
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  rw [hunion, Finset.sum_union (Finset.disjoint_sdiff)]
  have hlast : (∑ p ∈ (range (z + 1)).filter Nat.Prime \ ((range (n + 1)).filter (fun p => p ∈ A ∧ 3 * p < 2 * n)).filter
        (fun p => p % primorial z ∈ (range (primorial z)).filter
          (fun r => Odd r ∧ Nat.Coprime r (primorial z) ∧ r % 3 = u % 3)), Real.log p)
      ≤ ∑ p ∈ (range (z + 1)).filter Nat.Prime, Real.log p :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun i _ _ => Real.log_natCast_nonneg i)
  linarith


/-- The final purely numerical step: the `2 : 1` weighted pair of class averages exceeds `3/2`. -/
lemma master (n N δ Cz Su Sv Au Av du dv x c : ℝ)
    (hn : 0 < n) (hN : 0 < N) (hδ : 0 < δ) (hδ8 : δ ≤ 1 / 8)
    (hcz : 9 * Cz ≤ (δ / 100) * n) (h3n : 3 ≤ (δ / 100) * (2 * n))
    (hx3 : 2 * n ≤ 3 * x + 3)
    (hd : 3 / 2 + δ ≤ 2 * du + dv)
    (hSu : (du - δ / 100) * (1 - δ / 100) * x / 2 - Cz ≤ Su)
    (hSv : (dv - δ / 100) * (1 - δ / 100) * x / 2 - Cz ≤ Sv)
    (hcn : c * n = 3 * N)
    (hAu : c * Su - δ / 8 * N ≤ Au)
    (hAv : c * Sv - δ / 8 * N ≤ Av) :
    3 / 2 * N < 2 * Au + Av := by
  have hε0 : (0:ℝ) < 1 - δ / 100 := by linarith
  have hx0 : 0 ≤ x := by nlinarith
  -- step 1: combine the two class bounds
  have h1 : c * (2 * Su + Sv) - 3 * (δ / 8) * N ≤ 2 * Au + Av := by
    nlinarith [hAu, hAv]
  -- step 2: the class log sums
  have h2 : (2 * du + dv - 3 * (δ / 100)) * (1 - δ / 100) * x / 2 - 3 * Cz
      ≤ 2 * Su + Sv := by
    have e : 2 * ((du - δ / 100) * (1 - δ / 100) * x / 2 - Cz)
        + ((dv - δ / 100) * (1 - δ / 100) * x / 2 - Cz)
        = (2 * du + dv - 3 * (δ / 100)) * (1 - δ / 100) * x / 2 - 3 * Cz := by ring
    linarith [hSu, hSv, e]
  -- step 3: use the density hypothesis
  have h3 : (3 / 2 + δ - 3 * (δ / 100)) * (1 - δ / 100) * x / 2 - 3 * Cz
      ≤ 2 * Su + Sv := by
    have hle : 3 / 2 + δ - 3 * (δ / 100) ≤ 2 * du + dv - 3 * (δ / 100) := by linarith
    have hpos : 0 ≤ (1 - δ / 100) * x / 2 := by positivity
    nlinarith [h2, hle, hpos, hε0, hx0]
  -- step 4: multiply by `c = 3N/n`
  have hc0 : 0 < c := by
    have : c = 3 * N / n := by
      rw [← hcn]; field_simp
    rw [this]; positivity
  have h4 : c * ((3 / 2 + δ - 3 * (δ / 100)) * (1 - δ / 100) * x / 2 - 3 * Cz)
      - 3 * (δ / 8) * N ≤ 2 * Au + Av := by
    have := mul_le_mul_of_nonneg_left h3 hc0.le
    nlinarith [h1, this]
  -- step 5: substitute `c n = 3 N`
  have h5 : 3 * N * ((3 / 2 + δ - 3 * (δ / 100)) * (1 - δ / 100) * x / 2 - 3 * Cz)
      - 3 * (δ / 8) * N * n ≤ n * (2 * Au + Av) := by
    have := mul_le_mul_of_nonneg_left h4 hn.le
    have e : c * ((3 / 2 + δ - 3 * (δ / 100)) * (1 - δ / 100) * x / 2 - 3 * Cz) * n
        = 3 * N * ((3 / 2 + δ - 3 * (δ / 100)) * (1 - δ / 100) * x / 2 - 3 * Cz) := by
      calc c * ((3 / 2 + δ - 3 * (δ / 100)) * (1 - δ / 100) * x / 2 - 3 * Cz) * n
          = (c * n) * ((3 / 2 + δ - 3 * (δ / 100)) * (1 - δ / 100) * x / 2 - 3 * Cz) := by ring
        _ = 3 * N * ((3 / 2 + δ - 3 * (δ / 100)) * (1 - δ / 100) * x / 2 - 3 * Cz) := by
            rw [hcn]
    nlinarith [this, e]
  -- step 6: conclude
  have hxN : 3 * x ≥ 2 * n - 3 := by linarith
  set A := (3 / 2 + δ - 3 * (δ / 100)) * (1 - δ / 100) with hAdef
  have hApos : 0 < A := by simp only [hAdef]; nlinarith [hδ]
  have hAub : A ≤ 2 := by simp only [hAdef]; nlinarith [hδ, hδ8]
  have hB : δ / 2 ≤ A - 3 * δ / 8 - 3 / 2 := by
    simp only [hAdef]
    have expand : (3 / 2 + δ - 3 * (δ / 100)) * (1 - δ / 100) - 3 * δ / 8 - 3 / 2
        = δ / 2 + δ * (2 / 25 - 97 * δ / 10000) := by ring
    rw [expand]
    have h2 : 97 * δ / 10000 ≤ 2 / 25 := by nlinarith [hδ8]
    have h3 : 0 ≤ δ * (2 / 25 - 97 * δ / 10000) := by nlinarith [hδ.le, h2]
    linarith
  have hnd : 150 ≤ δ * n := by linarith [h3n]
  have hcz' : 900 * Cz ≤ δ * n := by linarith [hcz]
  have h5' : 3 * N * (A * x / 2 - 3 * Cz) - 3 * (δ / 8) * N * n ≤ n * (2 * Au + Av) := by
    rw [hAdef]; exact h5
  have hx' : A * (2 * n - 3) / 2 ≤ A * (3 * x) / 2 := by
    have h1 : (2 * n - 3) / 2 ≤ (3 * x) / 2 := by linarith
    calc A * (2 * n - 3) / 2 = A * ((2 * n - 3) / 2) := by ring
      _ ≤ A * ((3 * x) / 2) := mul_le_mul_of_nonneg_left h1 hApos.le
      _ = A * (3 * x) / 2 := by ring
  have hN' : N * (A * (2 * n - 3) / 2) ≤ 3 * N * (A * x / 2) := by
    have h2 : A * (3 * x) / 2 = 3 * (A * x / 2) := by ring
    nlinarith [hx', h2, hN]
  have h5e : 3 * N * (A * x / 2) - 9 * N * Cz - 3 * (δ / 8) * N * n ≤ n * (2 * Au + Av) := by
    nlinarith [h5']
  have h6 : N * n * A - 3 * N * A / 2 - 9 * N * Cz - 3 * (δ / 8) * N * n
      ≤ n * (2 * Au + Av) := by
    have e : N * (A * (2 * n - 3) / 2) = N * n * A - 3 * N * A / 2 := by ring
    linarith [hN', h5e, e]
  have h8 : N * n * (δ / 2) ≤ N * n * (A - 3 * δ / 8 - 3 / 2) := by
    have h0 : 0 ≤ N * n := by positivity
    exact mul_le_mul_of_nonneg_left hB h0
  have hgoal2 : n * (3 / 2 * N) < n * (2 * Au + Av) := by
    nlinarith [h6, h8, hAub, hnd, hcz', hN, hn]
  exact lt_of_mul_lt_mul_left hgoal2 hn.le

/-- Final step when the second class has vanishing density: only the first class is used. -/
lemma master2 (n N δ Cz Su Sv Au Av du dv x c : ℝ)
    (hn : 0 < n) (hN : 0 < N) (hδ : 0 < δ) (hδ8 : δ ≤ 1 / 8)
    (hcz : 9 * Cz ≤ (δ / 100) * n) (h3n : 3 ≤ (δ / 100) * (2 * n))
    (hx3 : 2 * n ≤ 3 * x + 3)
    (hd : 3 / 2 + δ ≤ 2 * du + dv) (hdv : dv ≤ δ / 100) (hdu1 : du ≤ 1)
    (hSu : (du - δ / 100) * (1 - δ / 100) * x / 2 - Cz ≤ Su)
    (hSv : 0 ≤ Sv)
    (hcn : c * n = 3 * N)
    (hAu : c * Su - δ / 8 * N ≤ Au)
    (hAv : c * Sv - δ / 8 * N ≤ Av) :
    3 / 2 * N < 2 * Au + Av := by
  have hε0 : (0:ℝ) < 1 - δ / 100 := by linarith
  have hx0 : 0 ≤ x := by nlinarith
  set A2 := 2 * (du - δ / 100) * (1 - δ / 100) with hAdef
  have hdu0 : δ / 100 < du := by linarith
  have hε0' : (0:ℝ) < 1 - δ / 100 := by linarith
  have hApos : 0 < A2 := by
    simp only [hAdef]
    have h : (0:ℝ) < du - δ / 100 := by linarith
    positivity
  have hAub : A2 ≤ 2 := by
    simp only [hAdef]
    have h2 : du - δ / 100 ≤ 1 := by linarith
    have h3 : (1 - δ / 100) ≤ 1 := by linarith
    nlinarith [h2, hdu0.le, h3, hδ]
  have hkey : (3 / 2 + δ - 3 * (δ / 100)) * (1 - δ / 100) ≤ A2 := by
    simp only [hAdef]
    have h2 : 3 / 2 + δ - 3 * (δ / 100) ≤ 2 * (du - δ / 100) := by linarith
    nlinarith [h2, hε0'.le]
  have hB : δ / 2 ≤ A2 - 3 * δ / 8 - 3 / 2 := by
    have expand : (3 / 2 + δ - 3 * (δ / 100)) * (1 - δ / 100) - 3 * δ / 8 - 3 / 2
        = δ * (29 / 50 - 97 * δ / 10000) := by ring
    have h2 : 97 * δ / 10000 ≤ 2 / 25 := by nlinarith [hδ8]
    have h3 : 0 ≤ δ * (2 / 25 - 97 * δ / 10000) := by nlinarith [hδ.le, h2]
    linarith
  have hnd : 150 ≤ δ * n := by linarith [h3n]
  have hcz' : 900 * Cz ≤ δ * n := by linarith [hcz]
  -- step 1
  have h1 : c * (2 * Su + Sv) - 3 * (δ / 8) * N ≤ 2 * Au + Av := by
    nlinarith [hAu, hAv]
  -- step 2: only the first class contributes
  have h2 : (A2) * x / 2 - 2 * Cz ≤ 2 * Su + Sv := by
    have e : A2 * x / 2 = (du - δ / 100) * (1 - δ / 100) * x := by
      simp only [hAdef]; ring
    have h2Su : 2 * ((du - δ / 100) * (1 - δ / 100) * x / 2 - Cz) ≤ 2 * Su := by linarith [hSu]
    linarith [h2Su, hSv, e]
  have hc0 : 0 < c := by
    have : c = 3 * N / n := by rw [← hcn]; field_simp
    rw [this]; positivity
  have h4 : c * (A2 * x / 2 - 2 * Cz) - 3 * (δ / 8) * N ≤ 2 * Au + Av := by
    have := mul_le_mul_of_nonneg_left h2 hc0.le
    nlinarith [h1, this]
  have h5 : 3 * N * (A2 * x / 2 - 2 * Cz) - 3 * (δ / 8) * N * n ≤ n * (2 * Au + Av) := by
    have := mul_le_mul_of_nonneg_left h4 hn.le
    have e : c * (A2 * x / 2 - 2 * Cz) * n = 3 * N * (A2 * x / 2 - 2 * Cz) := by
      calc c * (A2 * x / 2 - 2 * Cz) * n = (c * n) * (A2 * x / 2 - 2 * Cz) := by ring
        _ = 3 * N * (A2 * x / 2 - 2 * Cz) := by rw [hcn]
    nlinarith [this, e]
  have hxN : 3 * x ≥ 2 * n - 3 := by linarith
  have hx' : A2 * (2 * n - 3) / 2 ≤ A2 * (3 * x) / 2 := by
    have h1' : (2 * n - 3) / 2 ≤ (3 * x) / 2 := by linarith
    calc A2 * (2 * n - 3) / 2 = A2 * ((2 * n - 3) / 2) := by ring
      _ ≤ A2 * ((3 * x) / 2) := mul_le_mul_of_nonneg_left h1' hApos.le
      _ = A2 * (3 * x) / 2 := by ring
  have hN' : N * (A2 * (2 * n - 3) / 2) ≤ 3 * N * (A2 * x / 2) := by
    have h2' : A2 * (3 * x) / 2 = 3 * (A2 * x / 2) := by ring
    nlinarith [hx', h2', hN]
  have h5e : 3 * N * (A2 * x / 2) - 6 * N * Cz - 3 * (δ / 8) * N * n
      ≤ n * (2 * Au + Av) := by
    nlinarith [h5]
  have h6 : N * n * A2 - 3 * N * A2 / 2 - 6 * N * Cz - 3 * (δ / 8) * N * n
      ≤ n * (2 * Au + Av) := by
    have e : N * (A2 * (2 * n - 3) / 2) = N * n * A2 - 3 * N * A2 / 2 := by ring
    linarith [hN', h5e, e]
  have h8 : N * n * (δ / 2) ≤ N * n * (A2 - 3 * δ / 8 - 3 / 2) := by
    have h0 : 0 ≤ N * n := by positivity
    exact mul_le_mul_of_nonneg_left hB h0
  have hgoal2 : n * (3 / 2 * N) < n * (2 * Au + Av) := by
    nlinarith [h6, h8, hAub, hnd, hcz', hN, hn]
  exact lt_of_mul_lt_mul_left hgoal2 hn.le

/-- The `2 : 1` weighted pair of class averages exceeds `3/2`. -/
theorem alpha_pair_eventually (A : Set ℕ) (hA : A ⊆ P) (hz : 3 ≤ z)
    (hm : primorial z = 2 * m) (δ : ℝ) (hδ : 0 < δ) (hδ8 : δ ≤ 1 / 8)
    (u v : ℕ) (hu : u % 3 ≠ 0) (hv : v % 3 ≠ 0)
    (hd : 3 / 2 + δ ≤ 2 * lowerDensityRes A u 3 + lowerDensityRes A v 3) :
    ∀ᶠ n : ℕ in atTop, 3 / 2 <
      2 * alphaRes m (fun b => Profiles408.halfProfile A z n δ m b) ((u : ℕ) : ZMod 3)
        + alphaRes m (fun b => Profiles408.halfProfile A z n δ m b) ((v : ℕ) : ZMod 3) := by
  have hW : 0 < primorial z := primorial_pos z
  have hφ0 : (0 : ℝ) < ((primorial z).totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.2 hW
  have hdu1 : lowerDensityRes A u 3 ≤ 1 := lowerDensityRes_le_one A u 3
  have hdv1 : lowerDensityRes A v 3 ≤ 1 := lowerDensityRes_le_one A v 3
  have hdu0 : 0 < lowerDensityRes A u 3 := by linarith
  have hcu : 0 < lowerDensityRes A u 3 - δ / 100 := by linarith
  have hε : 0 < δ / 100 := by positivity
  have hε1 : δ / 100 < 1 := by linarith
  obtain ⟨Xu, hXu⟩ := LeanLab.DensityGoldbach.U1446.theta_A_lower A hA 3 u (by norm_num) (coprime_three u hu)
    (lowerDensityRes A u 3 - δ / 100) hcu (by linarith) (δ / 100) hε hε1
  obtain ⟨Xv, hXv⟩ : ∃ Xv : ℕ, δ / 100 < lowerDensityRes A v 3 → ∀ X : ℕ, Xv ≤ X →
      (lowerDensityRes A v 3 - δ / 100) * (1 - δ / 100) * (X : ℝ) / 2 ≤
        ∑ p ∈ (range (X + 1)).filter (fun p => p ∈ A ∧ p.Prime ∧ p % 3 = v % 3), Real.log p := by
    by_cases h : δ / 100 < lowerDensityRes A v 3
    · obtain ⟨Xv, hXv⟩ := LeanLab.DensityGoldbach.U1446.theta_A_lower A hA 3 v (by norm_num) (coprime_three v hv)
        (lowerDensityRes A v 3 - δ / 100) (by linarith) (by linarith) (δ / 100) hε hε1
      refine ⟨Xv, fun _ => ?_⟩
      rw [show Nat.totient 3 = 2 from by decide] at hXv
      exact hXv
    · exact ⟨0, fun h' => (h h').elim⟩
  set Cz := ∑ p ∈ (range (z + 1)).filter Nat.Prime, Real.log p with hCzdef
  have hCz0 : (0 : ℝ) ≤ Cz := Finset.sum_nonneg (fun i _ => Real.log_natCast_nonneg i)
  refine Filter.Eventually.mono
    (Filter.eventually_ge_atTop (max (3 * max Xu Xv + 3) (max (Nat.ceil (900 * Cz / δ) + 10)
      (Nat.ceil (150 / δ) + 10)))) ?_
  intro n hn
  have hn1 : 3 * max Xu Xv + 3 ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : Nat.ceil (900 * Cz / δ) + 10 ≤ n :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn3 : Nat.ceil (150 / δ) + 10 ≤ n :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hnpos : 0 < n := by omega
  set x := (2 * n - 1) / 3 with hxdef
  have hxX : Xu ≤ x := by omega
  have hxXv : Xv ≤ x := by omega
  have hxle : 3 * x ≤ 2 * n := by omega
  have hxlb : 2 * n ≤ 3 * x + 3 := by omega
  have hCz1 : 900 * Cz / δ ≤ (n : ℝ) := by
    have h : Nat.ceil (900 * Cz / δ) ≤ n := by omega
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast h)
  have h150 : 150 / δ ≤ (n : ℝ) := by
    have h : Nat.ceil (150 / δ) ≤ n := by omega
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast h)
  -- the constants
  set c : ℝ := 3 * ((primorial z).totient : ℝ) / (2 * n) with hcdef
  have hc0 : 0 < c := by positivity
  set N : ℕ := (primorial z).totient / 2 with hNdef
  have hN2 : 2 * (N : ℝ) = ((primorial z).totient : ℝ) := by
    have h2 : (primorial z).totient = 2 * N := by
      have hd2 : 2 ∣ (primorial z).totient := (Nat.totient_even (by
        have h3 : 3 ≤ primorial z :=
          Nat.le_of_dvd (primorial_pos z) (prime_dvd_primorial Nat.prime_three hz)
        omega)).two_dvd
      have := Nat.div_mul_cancel hd2
      rw [← hNdef] at this
      omega
    rw [h2]; push_cast; ring
  -- class sums
  have hcardu : #((unitsMod m).filter (fun b => b.val % 3 = u % 3)) = N := card_class hz hm u hu
  have hcardv : #((unitsMod m).filter (fun b => b.val % 3 = v % 3)) = N := card_class hz hm v hv
  -- pointwise bound on the profile over the reduced residues below `z#`
  have hpoint : ∀ r ∈ (range (primorial z)).filter
      (fun r => Odd r ∧ Nat.Coprime r (primorial z) ∧ r % 3 = u % 3),
      c * (∑ p ∈ (range (n + 1)).filter
        (fun p => p ∈ A ∧ p % primorial z = r % primorial z ∧ 3 * p < 2 * n), Real.log p) - δ / 8
        ≤ Profiles408.primeProfile A (primorial z) n δ r := by
    intro r hr
    have := le_max_left (c * (∑ p ∈ (range (n + 1)).filter
      (fun p => p ∈ A ∧ p % primorial z = r % primorial z ∧ 3 * p < 2 * n), Real.log p) - δ / 8) 0
    rw [Profiles408.primeProfile, ← hcdef]
    exact this
  -- the two class filters of `alphaRes`
  have hfiltu : (unitsMod m).filter (fun b => ((b.val : ℕ) : ZMod 3) = ((u : ℕ) : ZMod 3))
      = (unitsMod m).filter (fun b => b.val % 3 = u % 3) := by
    refine Finset.filter_congr ?_
    intro b _
    rw [ZMod.natCast_eq_natCast_iff, Nat.ModEq]
  have hfiltv : (unitsMod m).filter (fun b => ((b.val : ℕ) : ZMod 3) = ((v : ℕ) : ZMod 3))
      = (unitsMod m).filter (fun b => b.val % 3 = v % 3) := by
    refine Finset.filter_congr ?_
    intro b _
    rw [ZMod.natCast_eq_natCast_iff, Nat.ModEq]
  set Au := ∑ b ∈ (unitsMod m).filter (fun b => b.val % 3 = u % 3),
    Profiles408.halfProfile A z n δ m b with hAudef
  set Av := ∑ b ∈ (unitsMod m).filter (fun b => b.val % 3 = v % 3),
    Profiles408.halfProfile A z n δ m b with hAvdef
  have hαu : alphaRes m (fun b => Profiles408.halfProfile A z n δ m b) ((u : ℕ) : ZMod 3)
      = Au / (N : ℝ) := by
    rw [alphaRes, hfiltu, hcardu, hAudef]
  have hαv : alphaRes m (fun b => Profiles408.halfProfile A z n δ m b) ((v : ℕ) : ZMod 3)
      = Av / (N : ℝ) := by
    rw [alphaRes, hfiltv, hcardv, hAvdef]
  -- sums over the reduced residues below `z#`
  set Ru := (range (primorial z)).filter
    (fun r => Odd r ∧ Nat.Coprime r (primorial z) ∧ r % 3 = u % 3) with hRudef
  set Rv := (range (primorial z)).filter
    (fun r => Odd r ∧ Nat.Coprime r (primorial z) ∧ r % 3 = v % 3) with hRvdef
  set Su := ∑ r ∈ Ru, (∑ p ∈ (range (n + 1)).filter
    (fun p => p ∈ A ∧ p % primorial z = r % primorial z ∧ 3 * p < 2 * n), Real.log p) with hSudef
  set Sv := ∑ r ∈ Rv, (∑ p ∈ (range (n + 1)).filter
    (fun p => p ∈ A ∧ p % primorial z = r % primorial z ∧ 3 * p < 2 * n), Real.log p) with hvSdef
  have hpointv : ∀ r ∈ Rv,
      c * (∑ p ∈ (range (n + 1)).filter
        (fun p => p ∈ A ∧ p % primorial z = r % primorial z ∧ 3 * p < 2 * n), Real.log p) - δ / 8
        ≤ Profiles408.primeProfile A (primorial z) n δ r := by
    intro r hr
    have := le_max_left (c * (∑ p ∈ (range (n + 1)).filter
      (fun p => p ∈ A ∧ p % primorial z = r % primorial z ∧ 3 * p < 2 * n), Real.log p) - δ / 8) 0
    rw [Profiles408.primeProfile, ← hcdef]
    exact this
  -- pointwise bound on the profile over `Ru`
  have hpointu : ∀ r ∈ Ru,
      c * (∑ p ∈ (range (n + 1)).filter
        (fun p => p ∈ A ∧ p % primorial z = r % primorial z ∧ 3 * p < 2 * n), Real.log p) - δ / 8
        ≤ Profiles408.primeProfile A (primorial z) n δ r := by
    intro r hr
    have := le_max_left (c * (∑ p ∈ (range (n + 1)).filter
      (fun p => p ∈ A ∧ p % primorial z = r % primorial z ∧ 3 * p < 2 * n), Real.log p) - δ / 8) 0
    rw [Profiles408.primeProfile, ← hcdef]
    exact this
  -- lower bounds for the class log sums
  have hxlt : 3 * x < 2 * n := by omega
  have hxn : x ≤ n := by omega
  have hxu : Su ≥ (lowerDensityRes A u 3 - δ / 100) * (1 - δ / 100) * (x : ℝ) / 2 - Cz := by
    have h1 := hXu x hxX
    rw [show Nat.totient 3 = 2 from by decide] at h1
    have h3 := S_lower A hA hz n u x hxlt hxn
    simp only [hRudef, hSudef]
    linarith [h1, h3]
  have hxv : δ / 100 < lowerDensityRes A v 3 →
      Sv ≥ (lowerDensityRes A v 3 - δ / 100) * (1 - δ / 100) * (x : ℝ) / 2 - Cz := by
    intro hv'
    have h1 := hXv hv' x hxXv
    have h3 := S_lower A hA hz n v x hxlt hxn
    simp only [hRvdef, hvSdef]
    linarith [h1, h3]
  have hSv0 : 0 ≤ Sv := by
    simp only [hvSdef]
    exact Finset.sum_nonneg (fun r _ => Finset.sum_nonneg (fun p _ => Real.log_natCast_nonneg p))
  -- the profile sums
  have hcardRu : #Ru = N := by
    rw [hRudef]
    rw [← card_class_eq hz hm u, hcardu]
  have hcardRv : #Rv = N := by
    rw [hRvdef]
    rw [← card_class_eq hz hm v, hcardv]
  have hsumu : c * Su - δ / 8 * (N : ℝ) ≤ Au := by
    rw [hAudef]
    rw [sum_unit_class A hz hm n δ u]
    rw [← hRudef]
    have h1 : ∑ r ∈ Ru, (c * (∑ p ∈ (range (n + 1)).filter
        (fun p => p ∈ A ∧ p % primorial z = r % primorial z ∧ 3 * p < 2 * n), Real.log p) - δ / 8)
        = c * Su - δ / 8 * (N : ℝ) := by
      have h2 : ∑ r ∈ Ru, c * (∑ p ∈ (range (n + 1)).filter
          (fun p => p ∈ A ∧ p % primorial z = r % primorial z ∧ 3 * p < 2 * n), Real.log p)
          = c * Su := by
        rw [hSudef, Finset.mul_sum]
      rw [Finset.sum_sub_distrib, h2, Finset.sum_const, hcardRu, nsmul_eq_mul]
      ring
    linarith [h1, Finset.sum_le_sum hpointu]
  have hsumv : c * Sv - δ / 8 * (N : ℝ) ≤ Av := by
    rw [hAvdef]
    rw [sum_unit_class A hz hm n δ v]
    rw [← hRvdef]
    have h1 : ∑ r ∈ Rv, (c * (∑ p ∈ (range (n + 1)).filter
        (fun p => p ∈ A ∧ p % primorial z = r % primorial z ∧ 3 * p < 2 * n), Real.log p) - δ / 8)
        = c * Sv - δ / 8 * (N : ℝ) := by
      have h2 : ∑ r ∈ Rv, c * (∑ p ∈ (range (n + 1)).filter
          (fun p => p ∈ A ∧ p % primorial z = r % primorial z ∧ 3 * p < 2 * n), Real.log p)
          = c * Sv := by
        rw [hvSdef, Finset.mul_sum]
      rw [Finset.sum_sub_distrib, h2, Finset.sum_const, hcardRv, nsmul_eq_mul]
      ring
    linarith [h1, Finset.sum_le_sum hpointv]
  -- the final inequality
  have hNpos : (0:ℝ) < (N:ℝ) := by
    have h2 : (0:ℝ) < 2 * (N:ℝ) := by rw [hN2]; exact hφ0
    linarith
  have hcN : c / (N:ℝ) = 3 / (n:ℝ) := by
    have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hnpos
    rw [hcdef]
    field_simp
    linarith [hN2]
  -- each class average is bounded below
  have hAu : c * Su / (N:ℝ) - δ / 8 ≤ Au / (N:ℝ) := by
    have h1 : c * Su - δ / 8 * (N:ℝ) ≤ Au := hsumu
    have h2 : (c * Su - δ / 8 * (N:ℝ)) / (N:ℝ) ≤ Au / (N:ℝ) :=
      div_le_div_of_nonneg_right h1 hNpos.le
    have e : (c * Su - δ / 8 * (N:ℝ)) / (N:ℝ) = c * Su / (N:ℝ) - δ / 8 := by
      field_simp
    linarith
  have hAv : c * Sv / (N:ℝ) - δ / 8 ≤ Av / (N:ℝ) := by
    have h1 : c * Sv - δ / 8 * (N:ℝ) ≤ Av := hsumv
    have h2 : (c * Sv - δ / 8 * (N:ℝ)) / (N:ℝ) ≤ Av / (N:ℝ) :=
      div_le_div_of_nonneg_right h1 hNpos.le
    have e : (c * Sv - δ / 8 * (N:ℝ)) / (N:ℝ) = c * Sv / (N:ℝ) - δ / 8 := by
      field_simp
    linarith
  have hx3 : 2 * (n:ℝ) ≤ 3 * (x:ℝ) + 3 := by exact_mod_cast hxlb
  have hcz : 9 * Cz ≤ (δ / 100) * (n:ℝ) := by
    have h := hCz1
    rw [div_le_iff₀ hδ] at h
    nlinarith
  have h3n : 3 ≤ (δ / 100) * (2 * (n:ℝ)) := by
    have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hnpos
    have hδn : 150 ≤ δ * (n:ℝ) := by
      have h := h150
      rw [div_le_iff₀ hδ] at h
      linarith
    nlinarith
  have hcn : c * (n:ℝ) = 3 * (N:ℝ) := by
    have hn0 : (n:ℝ) ≠ 0 := by positivity
    have h := hcN
    rw [div_eq_iff hNpos.ne'] at h
    have := h
    field_simp at this
    linarith [h]
  rw [hαu, hαv]
  have efin : 2 * (Au / (N:ℝ)) + Av / (N:ℝ) = (2 * Au + Av) / (N:ℝ) := by
    field_simp
  rw [efin, lt_div_iff₀ hNpos]
  by_cases hv' : δ / 100 < lowerDensityRes A v 3
  · have hSv := hxv hv'
    exact master n N δ Cz Su Sv Au Av (lowerDensityRes A u 3) (lowerDensityRes A v 3) x c
      (by exact_mod_cast hnpos) hNpos hδ hδ8 hcz h3n hx3 hd hxu hSv hcn hsumu hsumv
  · have hdle : lowerDensityRes A v 3 ≤ δ / 100 := le_of_not_gt hv'
    exact master2 n N δ Cz Su Sv Au Av (lowerDensityRes A u 3) (lowerDensityRes A v 3) x c
      (by exact_mod_cast hnpos) hNpos hδ hδ8 hcz h3n hx3 hd hdle hdu1 hxu hSv0 hcn hsumu hsumv


end Alpha

end LocalProfileHelpers


/-- LEAF. Shao page 17 Lemma 4.6 at q = 5/2, citing Green
math/0302311 Lemma 6.6. The lab's Green66p uses expectation normalization;
scaling by 1/N gives Shao's probability weight normalization. -/
theorem restriction_five_halves : U1488.Green66p (5 / 2) := by
  sorry

/-- LEAF. Shao pages 15 to 16, equation 29 and the sentence defining alpha_i.
The prime number theorem in progressions turns the mod 3 density inequalities
and the mod W lower bound into a positive finite profile. No sumset conclusion
or transference theorem occurs here. -/
theorem local_profile (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 8)
    (z : ℕ) (hz : 3 ≤ z) (A : Set ℕ) (hA : A ⊆ P)
    (h1 : 3 / 2 + δ ≤ 2 * lowerDensityRes A 1 3 + lowerDensityRes A 2 3)
    (h2 : 3 / 2 + δ ≤ 2 * lowerDensityRes A 2 3 + lowerDensityRes A 1 3)
    (hlocal : ∀ b, b < primorial z → Nat.Coprime b (primorial z) →
      δ ≤ lowerDensityRes A b (primorial z)) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ m : ℕ, ∀ [NeZero m], m = primorial z / 2 →
      let f := Profiles408.halfProfile A z n δ m
      (∀ b, 0 ≤ f b ∧ f b ≤ 1) ∧ (∀ b ∈ unitsMod m, 0 < f b) ∧
      3 / 2 < 2 * alphaRes m f 1 + alphaRes m f 2 ∧
      3 / 2 < 2 * alphaRes m f 2 + alphaRes m f 1 := by

  have hWeven : primorial z = 2 * (primorial z / 2) := by
    have h2 : 2 ∣ primorial z := prime_dvd_primorial Nat.prime_two (by omega)
    omega
  haveI hNz : NeZero (primorial z / 2) := ⟨by
    rcases Nat.eq_zero_or_pos (primorial z / 2) with h0 | h0
    · rw [h0, mul_zero] at hWeven
      exact absurd hWeven (primorial_pos z).ne'
    · exact h0.ne'⟩
  obtain ⟨N1, hN1⟩ := profile_le_one A hA hz hWeven δ hδ hδsmall
  have hp := profile_pos_eventually A hA hz hWeven δ hδ hlocal
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.1 hp
  have ha12 := alpha_pair_eventually A hA hz hWeven δ hδ hδsmall 1 2 (by norm_num) (by norm_num) h1
  obtain ⟨N3, hN3⟩ := Filter.eventually_atTop.1 ha12
  have ha21 := alpha_pair_eventually A hA hz hWeven δ hδ hδsmall 2 1 (by norm_num) (by norm_num) h2
  obtain ⟨N4, hN4⟩ := Filter.eventually_atTop.1 ha21
  refine ⟨max (max N1 N2) (max N3 N4), fun n hn => ?_⟩
  have hn1 : N1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : N2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn3 : N3 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn4 : N4 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  refine fun m => ?_
  intro _ hm
  subst hm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b
    refine ⟨?_, hN1 n hn1 b⟩
    rw [Profiles408.halfProfile, Profiles408.primeProfile]
    exact le_max_right _ 0
  · intro b hb
    apply hN2 n hn2
    simpa only [unitsMod, Finset.mem_filter, Finset.mem_univ, true_and] using hb
  · exact hN3 n hn3
  · exact hN4 n hn4

section Lifting408b

open LeanLab.DensityGoldbach (IsSum3 unitsMod P)
open LeanLab.DensityGoldbach.U1446 (hatE avg lpHat nuW fA)
open LeanLab.DensityGoldbach.Profiles408 (halfProfile primeProfile oddRepresentative)
open scoped Classical

/-- A congruence modulo `M` together with `0 < a < b + M` and `b ≤ M` forces `a = b`. -/
lemma eq_of_modEq_of_bounds {M a b : ℕ} (hM : 0 < M) (h : a ≡ b [MOD M]) (hb : b ≤ M)
    (ha0 : 0 < a) (ha : a < b + M) : a = b := by
  have hmod : a % M = b % M := h
  rcases lt_or_eq_of_le hb with hlt | heq
  · have hb' : b % M = b := Nat.mod_eq_of_lt hlt
    have ha' : a % M = b := by rw [hb'] at hmod; exact hmod
    have hdiv := Nat.div_add_mod a M
    rw [ha'] at hdiv
    have hlt2 : M * (a / M) < M * 1 := by rw [mul_one]; omega
    have h1 : a / M = 0 := by
      rcases Nat.eq_zero_or_pos (a / M) with h0 | h0
      · exact h0
      · exfalso
        have := Nat.mul_lt_mul_left hM |>.mp hlt2
        omega
    rw [h1, mul_zero, zero_add] at hdiv
    exact hdiv.symm
  · have hmod0 : a % M = 0 := by rw [heq, Nat.mod_self] at hmod; exact hmod
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hmod0
    have hkpos : 0 < k := by rcases k with _ | k'; omega; omega
    have ha' : a < M * 2 := by rw [heq] at ha; omega
    have hlt2 : M * k < M * 2 := by rw [← hk]; exact ha' 
    have hk2 : k < 2 := (Nat.mul_lt_mul_left hM).mp hlt2
    have hk1 : k = 1 := by omega
    rw [hk, hk1, mul_one, heq]

/-- Sum of the three integers `W * nᵢ.val + bᵢ`, reduced modulo `N`, is `W * s + Σbᵢ`
when `n₁ + n₂ + n₃ = s` in `ZMod N`. -/
lemma three_sum_cast (W b₁ b₂ b₃ s : ℕ) {N : ℕ} [NeZero N] (n₁ n₂ n₃ : ZMod N)
    (hsum : n₁ + n₂ + n₃ = (s : ZMod N)) :
    (((W * n₁.val + b₁) + (W * n₂.val + b₂) + (W * n₃.val + b₃) : ℕ) : ZMod N)
      = ((W * s + (b₁ + b₂ + b₃) : ℕ) : ZMod N) := by
  push_cast
  simp only [ZMod.natCast_zmod_val]
  rw [← hsum]
  ring

/-- The same sum reduced modulo `W`. -/
lemma three_sum_modW (W b₁ b₂ b₃ : ℕ) {N : ℕ} [NeZero N] (n₁ n₂ n₃ : ZMod N) :
    ((W * n₁.val + b₁) + (W * n₂.val + b₂) + (W * n₃.val + b₃)) ≡
      (b₁ + b₂ + b₃) [MOD W] := by
  have h : (W * n₁.val + b₁) + (W * n₂.val + b₂) + (W * n₃.val + b₃) =
      (b₁ + b₂ + b₃) + W * (n₁.val + n₂.val + n₃.val) := by ring
  rw [h, Nat.ModEq]
  exact Nat.add_mul_mod_self_left _ _ _

/-- The odd representatives of a triple summing to `n` modulo `m = z#/2` sum to `n`
modulo `z#`. -/
lemma oddRep_sum_modW {z m n : ℕ} [NeZero m] (hz : 3 ≤ z) (hm : primorial z = 2 * m)
    (hn : Odd n) (b₁ b₂ b₃ : ZMod m) (hb : (n : ZMod m) = b₁ + b₂ + b₃) :
    (oddRepresentative m b₁ + oddRepresentative m b₂ + oddRepresentative m b₃) ≡ n
      [MOD primorial z] := by
  have hoddm : Odd m := odd_of_w hz hm
  obtain ⟨-, hodd1, hmod1, -⟩ := oddRep_props hz hm b₁
  obtain ⟨-, hodd2, hmod2, -⟩ := oddRep_props hz hm b₂
  obtain ⟨-, hodd3, hmod3, -⟩ := oddRep_props hz hm b₃
  -- congruence modulo `m`
  have hcast : ((b₁.val + b₂.val + b₃.val : ℕ) : ZMod m) = (n : ZMod m) := by
    push_cast
    simp only [ZMod.natCast_zmod_val]
    exact hb.symm
  have hm1 : (b₁.val + b₂.val + b₃.val) ≡ n [MOD m] := ZMod.natCast_eq_natCast_iff _ _ _ |>.1 hcast
  have hrep1 : oddRepresentative m b₁ ≡ b₁.val [MOD m] := by
    rw [Nat.ModEq, hmod1, Nat.mod_eq_of_lt (ZMod.val_lt b₁)]
  have hrep2 : oddRepresentative m b₂ ≡ b₂.val [MOD m] := by
    rw [Nat.ModEq, hmod2, Nat.mod_eq_of_lt (ZMod.val_lt b₂)]
  have hrep3 : oddRepresentative m b₃ ≡ b₃.val [MOD m] := by
    rw [Nat.ModEq, hmod3, Nat.mod_eq_of_lt (ZMod.val_lt b₃)]
  have hsum : (oddRepresentative m b₁ + oddRepresentative m b₂ + oddRepresentative m b₃) ≡
      n [MOD m] := ((hrep1.add hrep2).add hrep3).trans hm1
  -- congruence modulo `2`
  have hpar : (oddRepresentative m b₁ + oddRepresentative m b₂ + oddRepresentative m b₃) ≡
      n [MOD 2] := by
    have h2 : (oddRepresentative m b₁ + oddRepresentative m b₂ + oddRepresentative m b₃) % 2 = 1 := by
      have : Odd (oddRepresentative m b₁ + oddRepresentative m b₂ + oddRepresentative m b₃) :=
        (hodd1.add_odd hodd2).add_odd hodd3
      exact Nat.odd_iff.1 this
    rw [Nat.ModEq, h2, Nat.odd_iff.1 hn]
  -- combine
  have hcop : Nat.Coprime m 2 := (Nat.coprime_two_left.mpr hoddm).symm
  have := (Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨hsum, hpar⟩
  rwa [show m * 2 = primorial z by omega] at this

/-- The end of the lifting argument: three primes in `A 0`, `A 1`, `A 2` whose sum is congruent
to `n` modulo `z# * N`, each below `Xc`, with `3 * Xc < 2 * n` and `n ≤ z# * N`, sum to `n`. -/
lemma IsSum3_of_congruent {z N n Xc : ℕ} [NeZero N] {A : Fin 3 → Set ℕ} {p₀ p₁ p₂ : ℕ}
    (hWN : n ≤ primorial z * N) (hXc : 3 * Xc < 2 * n)
    (b1 : p₀ ≤ Xc) (b2 : p₁ ≤ Xc) (b3 : p₂ ≤ Xc)
    (h0 : p₀ ∈ A 0) (h1 : p₁ ∈ A 1) (h2 : p₂ ∈ A 2)
    (hpos : 0 < p₀) (hcong : p₀ + p₁ + p₂ ≡ n [MOD primorial z * N]) :
    IsSum3 (A 0) (A 1) (A 2) n := by
  have hM : 0 < primorial z * N := by
    have := primorial_pos z
    have : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
    positivity
  have hlt : p₀ + p₁ + p₂ < 2 * n := by omega
  have heq : p₀ + p₁ + p₂ = n :=
    eq_of_modEq_of_bounds hM hcong hWN (by omega) (by omega)
  exact ⟨p₀, h0, p₁, h1, p₂, h2, by omega⟩


/-! ## Profile layer: positive profile gives mass to the class -/

/-- From a positive profile the class log sum over the cutoff is at least `δ n / (12 φ(W))`. -/
lemma class_sum_lower {A : Set ℕ} {z n : ℕ} {δ : ℝ} {m : ℕ} [NeZero m] {b : ZMod m}
    (hn : 0 < n) (h : 0 < halfProfile A z n δ m b) :
    δ * (n : ℝ) / (12 * ((primorial z).totient : ℝ)) <
      ∑ p ∈ (range (n + 1)).filter (fun p => p ∈ A ∧
        p % primorial z = (oddRepresentative m b) % primorial z ∧ 3 * p < 2 * n), Real.log p := by
  set S : ℝ := ∑ p ∈ (range (n + 1)).filter (fun p => p ∈ A ∧
      p % primorial z = (oddRepresentative m b) % primorial z ∧ 3 * p < 2 * n), Real.log p
  set φ : ℝ := ((primorial z).totient : ℝ)
  have hW : 0 < primorial z := primorial_pos z
  have hφ : 0 < φ := by
    simp only [φ]; exact_mod_cast Nat.totient_pos.2 hW
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hmax : 0 < max ((3 * φ / (2 * (n : ℝ))) * S - (δ / 8)) 0 := by
    rw [halfProfile, primeProfile] at h
    simpa only [φ, S] using h
  have hX : 0 < (3 * φ / (2 * (n : ℝ))) * S - (δ / 8) := by
    rcases lt_max_iff.1 hmax with h' | h'
    · exact h'
    · linarith
  have hX2 : δ / 8 < (3 * φ / (2 * (n : ℝ))) * S := by linarith
  have hpos : (0 : ℝ) < 2 * (n : ℝ) / (3 * φ) := by positivity
  have hstep := mul_lt_mul_of_pos_right hX2 hpos
  have e2 : ((3 * φ / (2 * (n : ℝ))) * S) * (2 * (n : ℝ) / (3 * φ)) = S := by
    field_simp
  have e1 : (δ / 8) * (2 * (n : ℝ) / (3 * φ)) = δ * (n : ℝ) / (12 * φ) := by
    field_simp
    ring
  rw [e2, e1] at hstep
  exact hstep


/-- The profile cutoff `3 p < 2 n` is the truncation at `(2 n - 1) / 3`. -/
lemma profile_sum_eq (A : Set ℕ) (hA : A ⊆ P) {z n : ℕ} (hn : 0 < n) (b : ℕ) :
    (∑ p ∈ (range (n + 1)).filter (fun p => p ∈ A ∧
        p % primorial z = b % primorial z ∧ 3 * p < 2 * n), Real.log p) =
      ∑ p ∈ (range ((2 * n - 1) / 3 + 1)).filter (fun p => p ∈ A ∧ p.Prime ∧
        p % primorial z = b % primorial z), Real.log p := by
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext p
  simp only [mem_filter, mem_range]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, h2, show Nat.Prime p from hA h2, h3⟩
    have hle : p * 3 ≤ 2 * n - 1 := by omega
    have hstep : p ≤ (2 * n - 1) / 3 := (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).2 hle
    omega
  · rintro ⟨h1, h2, h3, h4⟩
    have hstep : p ≤ (2 * n - 1) / 3 := by omega
    have hle : p * 3 ≤ 2 * n - 1 := (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).1 hstep
    exact ⟨by omega, h2, h4, by omega⟩

/-- The mass of the truncated class weight is `(φ(W)/W)` times the class log sum. -/
lemma sum_fA_eq (A : Set ℕ) (hA : A ⊆ P) {z n N : ℕ} (hn : 0 < n) [NeZero N] (b : ℕ)
    (hb : b < primorial z) (hX : (2 * n - 1) / 3 < primorial z * N) :
    ∑ x : ZMod N, fA A (primorial z) b ((2 * n - 1) / 3) N x =
      ((primorial z).totient : ℝ) / (primorial z) *
        ∑ p ∈ (range ((2 * n - 1) / 3 + 1)).filter (fun p => p ∈ A ∧ p.Prime ∧
          p % primorial z = b % primorial z), Real.log p := by
  have hW : 0 < primorial z := primorial_pos z
  have hN : (N : ℝ) ≠ 0 := by
    have : N ≠ 0 := NeZero.ne N
    exact_mod_cast this
  have h1 : (N : ℝ) * avg N (fA A (primorial z) b ((2 * n - 1) / 3) N) =
      ∑ x : ZMod N, fA A (primorial z) b ((2 * n - 1) / 3) N x := by
    unfold avg
    field_simp
  rw [← h1, LeanLab.DensityGoldbach.U1446.avg_fA A hA (primorial z) b ((2 * n - 1) / 3) N hb hX]
  field_simp

/-- The profile is monotone in the density parameter. -/
lemma profile_mono_le {A : Set ℕ} {z n : ℕ} {δ δ' : ℝ} {m : ℕ} [NeZero m] {b : ZMod m}
    (h : δ' ≤ δ) : halfProfile A z n δ m b ≤ halfProfile A z n δ' m b := by
  simp only [halfProfile, primeProfile]
  exact max_le_max (by linarith) le_rfl

/-- A positive profile equals its `max` expression. -/
lemma profile_eq_of_pos {A : Set ℕ} {z n : ℕ} {δ : ℝ} {m : ℕ} [NeZero m] {b : ZMod m}
    (h : 0 < halfProfile A z n δ m b) :
    halfProfile A z n δ m b = (3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ))) *
      (∑ p ∈ (range (n + 1)).filter (fun p => p ∈ A ∧
        p % primorial z = (oddRepresentative m b) % primorial z ∧ 3 * p < 2 * n),
        Real.log p) - δ / 8 := by
  have h' : 0 < max ((3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ))) *
      (∑ p ∈ (range (n + 1)).filter (fun p => p ∈ A ∧
        p % primorial z = (oddRepresentative m b) % primorial z ∧ 3 * p < 2 * n),
        Real.log p) - δ / 8) 0 := by
    rw [halfProfile, primeProfile] at h; exact h
  rw [halfProfile, primeProfile, max_eq_left (le_of_lt (lt_max_iff.1 h' |>.resolve_right (by linarith)))]

/-! ## Arithmetic core of the mass bounds -/

/-- A single class mass is at least `d / 24`. -/
lemma mass_lower {d φ S W N n : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (hφ : 0 < φ) (hW : 0 < W)
    (hN : 0 < N) (hWN : W * N ≤ (1 + d / 8) * n) (hS : d * n / (12 * φ) < S) :
    d / 24 ≤ φ / (W * N) * S := by
  have hWN0 : 0 < W * N := mul_pos hW hN
  have h1 : φ / (W * N) * (d * n / (12 * φ)) < φ / (W * N) * S :=
    mul_lt_mul_of_pos_left hS (by positivity)
  have h2 : φ / (W * N) * (d * n / (12 * φ)) = d / 12 * (n / (W * N)) := by
    field_simp
  rw [h2] at h1
  have h4 : 1 / (1 + d / 8) ≤ n / (W * N) := by
    rw [div_le_div_iff₀ (by positivity) hWN0]
    nlinarith [hWN]
  have h5 : d / 12 * (1 / (1 + d / 8)) ≤ d / 12 * (n / (W * N)) :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  have h6 : d / 24 ≤ d / 12 * (1 / (1 + d / 8)) := by
    rw [mul_one_div, le_div_iff₀ (by positivity)]
    nlinarith [hd, hd1]
  linarith [h1, h5, h6]

/-- The total mass exceeds `1` by at least `d / 24`. -/
lemma total_lower {d φ S W N n : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (hφ : 0 < φ) (hW : 0 < W)
    (hN : 0 < N) (hn : 0 < n) (hWN : W * N ≤ (1 + d / 8) * n)
    (hS : 3 / 2 + 3 * d / 8 < (3 * φ / (2 * n)) * S) :
    d / 24 ≤ φ / (W * N) * S - 1 := by
  have hWN0 : 0 < W * N := mul_pos hW hN
  have hconv : (3 / 2 + 3 * d / 8) * (2 * n / (3 * φ)) < S := by
    have h := mul_lt_mul_of_pos_right hS (by positivity : (0 : ℝ) < 2 * n / (3 * φ))
    have e2 : (3 * φ / (2 * n) * S) * (2 * n / (3 * φ)) = S := by
      field_simp
    rw [e2] at h
    exact h
  have hval : (3 / 2 + 3 * d / 8) * (2 * n / (3 * φ)) = n * (1 + d / 4) / φ := by
    field_simp
    ring
  rw [hval] at hconv
  have h1 : φ / (W * N) * (n * (1 + d / 4) / φ) < φ / (W * N) * S :=
    mul_lt_mul_of_pos_left hconv (by positivity)
  have h2 : φ / (W * N) * (n * (1 + d / 4) / φ) = (1 + d / 4) * (n / (W * N)) := by
    field_simp
  rw [h2] at h1
  have h4 : 1 / (1 + d / 8) ≤ n / (W * N) := by
    rw [div_le_div_iff₀ (by positivity) hWN0]
    nlinarith [hWN]
  have h5 : (1 + d / 4) * (1 / (1 + d / 8)) ≤ (1 + d / 4) * (n / (W * N)) :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  have h6 : d / 24 ≤ (1 + d / 4) * (1 / (1 + d / 8)) - 1 := by
    rw [mul_one_div, div_sub_one (by positivity), le_div_iff₀ (by positivity)]
    nlinarith [hd, hd1]
  linarith [h1, h5, h6]


/-! ## The lifting step -/

/-- A positive truncated class weight puts `W * n.val + b` in `A` below `X`. -/
lemma fA_pos_of_pos {A : Set ℕ} {W b X N : ℕ} [NeZero N] {x : ZMod N}
    (h : 0 < fA A W b X N x) : W * x.val + b ∈ A ∧ W * x.val + b ≤ X := by
  unfold fA at h
  split_ifs at h with hc
  · exact hc
  · exact absurd h (lt_irrefl 0)

/-- Shao's local lifting step, from the transference principle and the restriction
estimate at the exponent `5/2`. -/
theorem weighted_lifting_mixed_proof (H : AlsetriProp41) (R : U1488.Green66p (5 / 2))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ z₀ : ℕ, 3 ≤ z₀ ∧ ∀ z : ℕ, z₀ ≤ z → ∀ A : Fin 3 → Set ℕ, (∀ i, A i ⊆ P) →
      ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Odd n → ∀ m : ℕ, ∀ [NeZero m],
        m = primorial z / 2 → ∀ b₁ ∈ unitsMod m, ∀ b₂ ∈ unitsMod m, ∀ b₃ ∈ unitsMod m,
        (n : ZMod m) = b₁ + b₂ + b₃ →
        0 < halfProfile (A 0) z n δ m b₁ →
        0 < halfProfile (A 1) z n δ m b₂ →
        0 < halfProfile (A 2) z n δ m b₃ →
        3 / 2 < halfProfile (A 0) z n δ m b₁ + halfProfile (A 1) z n δ m b₂ +
          halfProfile (A 2) z n δ m b₃ →
        IsSum3 (A 0) (A 1) (A 2) n := by
  set d : ℝ := min δ 1 with hddef
  have hd : 0 < d := lt_min hδ one_pos
  have hdd : d ≤ δ := min_le_left _ _
  have hd1 : d ≤ 1 := min_le_right _ _
  obtain ⟨C, hC, zR, hR⟩ := R
  obtain ⟨c, hc, hH⟩ := H (d / 24) (by positivity)
  obtain ⟨η, hη, NH, hH1⟩ := hH (5 / 2) (by norm_num) (by norm_num) (max C 1)
    (lt_of_lt_of_le hC (le_max_left _ _))
  obtain ⟨zG, hG⟩ := LeanLab.DensityGoldbach.U1446.nu_fourier
    LeanLab.DensityGoldbach.U1484.green62 η hη
  obtain ⟨YP, hYP⟩ := LeanLab.DensityGoldbach.U1446.exists_prime_between (d / 8)
    (by positivity) (by linarith : d / 8 ≤ 1)
  refine ⟨max (max zR zG) 3, le_max_right _ _, ?_⟩
  intro z hz A hA
  have hz3 : 3 ≤ z := le_trans (le_max_right _ _) hz
  have hzR : zR ≤ z := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hz
  have hzG : zG ≤ z := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hz
  have hW : 0 < primorial z := primorial_pos z
  have hWr : (0 : ℝ) < (primorial z : ℝ) := by exact_mod_cast hW
  have hφ : (0 : ℝ) < ((primorial z).totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.2 hW
  -- thresholds, uniform over the finitely many classes `b < z#`
  have hNGex : ∀ b : ℕ, ∃ N₀ : ℕ, b < primorial z → Nat.Coprime b (primorial z) →
      ∀ N : ℕ, ∀ [NeZero N], N.Prime → N₀ ≤ N → ∀ r : ZMod N,
        ‖hatE N (nuW (primorial z) b N) r - (if r = 0 then 1 else 0)‖ ≤ η := by
    intro b
    by_cases hb : b < primorial z ∧ Nat.Coprime b (primorial z)
    · obtain ⟨N₀, hN₀⟩ := hG z hzG b hb.1 hb.2
      exact ⟨N₀, fun _ _ => hN₀⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hb⟩
  choose NG hNG using hNGex
  have hNRex : ∀ b : ℕ, ∃ N₀ : ℕ, b < primorial z → Nat.Coprime b (primorial z) →
      ∀ N : ℕ, ∀ [NeZero N], N.Prime → N₀ ≤ N → ∀ (f : ZMod N → ℝ),
        (∀ n, 0 ≤ f n ∧ f n ≤ nuW (primorial z) b N n) → lpHat N (5 / 2) f ≤ C := by
    intro b
    by_cases hb : b < primorial z ∧ Nat.Coprime b (primorial z)
    · obtain ⟨N₀, hN₀⟩ := hR z hzR b hb.1 hb.2
      exact ⟨N₀, fun _ _ => hN₀⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hb⟩
  choose NR hNR using hNRex
  set K : ℕ := max (max (max NH (Finset.sup (range (primorial z)) NG))
    (Finset.sup (range (primorial z)) NR)) 1 with hKdef
  have hsupG : Finset.sup (range (primorial z)) NG ≤ K := by
    rw [hKdef]
    exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hsupR : Finset.sup (range (primorial z)) NR ≤ K := by
    rw [hKdef]
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hNHK : NH ≤ K := by
    rw [hKdef]
    exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have hK1 : 1 ≤ K := by rw [hKdef]; exact le_max_right _ _
  refine ⟨⌈(max YP 0 + (K : ℝ)) * ((primorial z : ℝ) + 1)⌉₊ + ((z + 1) * primorial z + 2), ?_⟩
  intro n hn hodd m inst hm b₁ hb₁ b₂ hb₂ b₃ hb₃ hnb hp₁ hp₂ hp₃ hsum3
  -- large-`n` consequences
  have hceil : ((⌈(max YP 0 + (K : ℝ)) * ((primorial z : ℝ) + 1)⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by
    have h1 : ⌈(max YP 0 + (K : ℝ)) * ((primorial z : ℝ) + 1)⌉₊ ≤ n := by omega
    exact_mod_cast h1
  have hbig : (max YP 0 + (K : ℝ)) * ((primorial z : ℝ) + 1) ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil _) hceil
  have hzw : ((z + 1) * primorial z : ℕ) + 2 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hnpos : 0 < n := by omega
  have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hY0 : (0 : ℝ) ≤ max YP 0 := le_max_right _ _
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := by positivity
  -- the prime of the window
  have hyP : YP ≤ (n : ℝ) / (primorial z) := by
    rw [le_div_iff₀ hWr]
    nlinarith [hbig, le_max_left YP (0 : ℝ), hWr, hY0, hK0]
  obtain ⟨N, hNp, hNlow, hNhigh⟩ := hYP _ hyP
  have hNpos : 0 < N := hNp.pos
  haveI : NeZero N := ⟨hNpos.ne'⟩
  haveI : Fact N.Prime := ⟨hNp⟩
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hnWN : n ≤ primorial z * N := by
    have h1 : (n : ℝ) ≤ (primorial z : ℝ) * N := by
      rw [div_le_iff₀ hWr] at hNlow
      linarith
    exact_mod_cast h1
  have hWNle : (primorial z : ℝ) * N ≤ (1 + d / 8) * (n : ℝ) := by
    have h2 : (primorial z : ℝ) * ((n : ℝ) / (primorial z : ℝ)) = (n : ℝ) := by
      field_simp
    nlinarith [hNhigh, hWr, h2]
  have hNK : K ≤ N := by
    have h1 : (K : ℝ) ≤ (n : ℝ) / (primorial z) := by
      rw [le_div_iff₀ hWr]
      nlinarith [hbig, hY0, hK0, hWr]
    have := le_trans h1 hNlow
    exact_mod_cast this
  have hzN : z < N := by
    have h1 : ((z + 1) * primorial z : ℕ) ≤ n := by omega
    have h2 : ((z + 1) * (primorial z) : ℕ) ≤ primorial z * N := le_trans h1 hnWN
    have h3 : z + 1 ≤ N := by
      rcases Nat.eq_zero_or_pos (primorial z) with h0 | h0
      · rw [h0] at h2; omega
      · exact Nat.le_of_mul_le_mul_left (by simpa only [mul_comm] using h2) h0
    omega
  have hNdvd : ¬ N ∣ primorial z := by
    intro hd
    have := (Nat.Prime.dvd_primorial_iff hNp).1 hd
    omega
  have hcopWN : Nat.Coprime (primorial z) N := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hNp]
    exact hNdvd
  -- bookkeeping
  set bb : Fin 3 → ZMod m := ![b₁, b₂, b₃] with hbbdef
  have hbb0 : bb 0 = b₁ := by simp [hbbdef]
  have hbb1 : bb 1 = b₂ := by simp [hbbdef]
  have hbb2 : bb 2 = b₃ := by simp [hbbdef]
  have hposδ : ∀ i, 0 < halfProfile (A i) z n δ m (bb i) := by
    intro i
    fin_cases i
    · simpa [hbb0] using hp₁
    · simpa [hbb1] using hp₂
    · simpa [hbb2] using hp₃
  have hposd : ∀ i, 0 < halfProfile (A i) z n d m (bb i) := fun i =>
    lt_of_lt_of_le (hposδ i) (profile_mono_le hdd)
  have hsumd : 3 / 2 < ∑ i : Fin 3, halfProfile (A i) z n d m (bb i) := by
    rw [Fin.sum_univ_three]
    exact lt_of_lt_of_le (by simpa only [hbb0, hbb1, hbb2] using hsum3)
      (add_le_add (add_le_add (profile_mono_le hdd) (profile_mono_le hdd)) (profile_mono_le hdd))
  have hunits : ∀ i, IsUnit (bb i) := by
    intro i
    fin_cases i
    · simpa [hbb0, unitsMod] using hb₁
    · simpa [hbb1, unitsMod] using hb₂
    · simpa [hbb2, unitsMod] using hb₃
  have hW2m : primorial z = 2 * m := by
    have h2 : 2 ∣ primorial z := prime_dvd_primorial Nat.prime_two (by omega)
    omega
  set bp : Fin 3 → ℕ := fun i => oddRepresentative m (bb i) with hbpdef
  have hbplt : ∀ i, bp i < primorial z := by
    intro i
    exact (oddRep_props hz3 hW2m (bb i)).1
  have hbpcop : ∀ i, Nat.Coprime (bp i) (primorial z) := fun i =>
    oddRep_coprime hz3 hW2m (bb i) (hunits i)
  have hnb' : (n : ZMod m) = bb 0 + bb 1 + bb 2 := by
    simpa only [hbb0, hbb1, hbb2] using hnb
  -- the two weight families on `ZMod N`
  set ν : Fin 3 → ZMod N → ℝ := fun i x => nuW (primorial z) (bp i) N x / N with hνdef
  set fv : Fin 3 → ZMod N → ℝ := fun i x =>
    fA (A i) (primorial z) (bp i) ((2 * n - 1) / 3) N x / N with hfvdef
  have hνapp : ∀ i x, ν i x = nuW (primorial z) (bp i) N x / N := fun i x => by rw [hνdef]
  have hfvapp : ∀ i x, fv i x =
      fA (A i) (primorial z) (bp i) ((2 * n - 1) / 3) N x / N := fun i x => by rw [hfvdef]
  have hXci : (2 * n - 1) / 3 < primorial z * N := by
    have h1 : (2 * n - 1) / 3 < n := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 3)]
      omega
    exact lt_of_lt_of_le h1 hnWN
  -- (4.1)
  have hbound : ∀ i x, 0 ≤ fv i x ∧ fv i x ≤ ν i x := by
    intro i x
    rw [hfvapp, hνapp]
    refine ⟨div_nonneg (LeanLab.DensityGoldbach.U1446.fA_nonneg _ _ _ _ _ _) (by positivity), ?_⟩
    exact div_le_div_of_nonneg_right
      (LeanLab.DensityGoldbach.U1446.fA_le_nuW (A i) (hA i) _ _ _ _ _) (by positivity)
  -- class log sums
  have hS : ∀ i, d * (n : ℝ) / (12 * ((primorial z).totient : ℝ)) <
      ∑ p ∈ (range ((2 * n - 1) / 3 + 1)).filter (fun p => p ∈ A i ∧ p.Prime ∧
        p % primorial z = (bp i) % primorial z), Real.log p := by
    intro i
    refine lt_of_lt_of_le (class_sum_lower hnpos (hposd i)) (le_of_eq ?_)
    exact profile_sum_eq (A i) (hA i) hnpos (bp i)
  -- (4.2a)
  have hmassGe : ∀ i, d / 24 ≤ ∑ x : ZMod N, fv i x := by
    intro i
    have h1 : ∑ x : ZMod N, fv i x = ((primorial z).totient : ℝ) / (primorial z * N) *
        (∑ p ∈ (range ((2 * n - 1) / 3 + 1)).filter (fun p => p ∈ A i ∧ p.Prime ∧
          p % primorial z = (bp i) % primorial z), Real.log p) := by
      simp only [hfvdef]
      rw [← Finset.sum_div, sum_fA_eq (A i) (hA i) hnpos (bp i) (hbplt i) hXci]
      field_simp
    rw [h1]
    exact mass_lower hd hd1 hφ hWr hNr hWNle (hS i)
  -- (4.2b)
  have htotGe : d / 24 ≤ (∑ i : Fin 3, ∑ x : ZMod N, fv i x) - 1 := by
    set S : ℝ := ∑ p ∈ (range ((2 * n - 1) / 3 + 1)).filter (fun p => p ∈ A 0 ∧ p.Prime ∧
      p % primorial z = (bp 0) % primorial z), Real.log p +
      ∑ p ∈ (range ((2 * n - 1) / 3 + 1)).filter (fun p => p ∈ A 1 ∧ p.Prime ∧
        p % primorial z = (bp 1) % primorial z), Real.log p +
      ∑ p ∈ (range ((2 * n - 1) / 3 + 1)).filter (fun p => p ∈ A 2 ∧ p.Prime ∧
        p % primorial z = (bp 2) % primorial z), Real.log p with hSdef
    have hprof : ∀ i, halfProfile (A i) z n d m (bb i) =
        (3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ))) *
          (∑ p ∈ (range ((2 * n - 1) / 3 + 1)).filter (fun p => p ∈ A i ∧ p.Prime ∧
            p % primorial z = (bp i) % primorial z), Real.log p) - d / 8 := by
      intro i
      refine (profile_eq_of_pos (hposd i)).trans ?_
      rw [profile_sum_eq (A i) (hA i) hnpos (bp i)]
    have hsum3' : 3 / 2 + 3 * d / 8 < (3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ))) * S := by
      have hpe : ∑ i : Fin 3, halfProfile (A i) z n d m (bb i) =
          (3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ))) * S - 3 * (d / 8) := by
        rw [hSdef, Fin.sum_univ_three, hprof 0, hprof 1, hprof 2]
        ring
      rw [hpe] at hsumd
      linarith
    have hmtot : ∑ i : Fin 3, ∑ x : ZMod N, fv i x =
        ((primorial z).totient : ℝ) / (primorial z * N) * S := by
      have h1 : ∀ i, ∑ x : ZMod N, fv i x = ((primorial z).totient : ℝ) / (primorial z * N) *
          (∑ p ∈ (range ((2 * n - 1) / 3 + 1)).filter (fun p => p ∈ A i ∧ p.Prime ∧
            p % primorial z = (bp i) % primorial z), Real.log p) := by
        intro i
        simp only [hfvdef]
        rw [← Finset.sum_div, sum_fA_eq (A i) (hA i) hnpos (bp i) (hbplt i) hXci]
        field_simp
      rw [Finset.sum_congr rfl fun i _ => h1 i, Fin.sum_univ_three, hSdef]
      ring
    rw [hmtot]
    exact total_lower hd hd1 hφ hWr hNr hnr hWNle hsum3'
  -- (4.3)
  have hfourier : ∀ i (r : ZMod N),
      ‖fourierZN N (ν i) r - (if r = 0 then 1 else 0)‖ ≤ η := by
    intro i r
    have hle : NG (bp i) ≤ N := by
      refine le_trans (le_trans (Finset.le_sup (f := NG) (mem_range.2 (hbplt i))) hsupG) hNK
    have h := hNG (bp i) (hbplt i) (hbpcop i) N hNp hle (-r)
    rw [hνdef, LeanLab.DensityGoldbach.Smoothing408.probability_transform]
    simpa only [neg_eq_zero] using h
  -- (4.4)
  have hnorm : ∀ i, (∑ r : ZMod N, ‖fourierZN N (fv i) r‖ ^ (5 / 2 : ℝ)) ^
      (1 / (5 / 2 : ℝ)) ≤ max C 1 := by
    intro i
    have hle : NR (bp i) ≤ N := by
      refine le_trans (le_trans (Finset.le_sup (f := NR) (mem_range.2 (hbplt i))) hsupR) hNK
    have h1 : lpHat N (5 / 2) (fun x => fA (A i) (primorial z) (bp i) ((2 * n - 1) / 3) N x) ≤ C :=
      hNR (bp i) (hbplt i) (hbpcop i) N hNp hle _
        (fun x => ⟨LeanLab.DensityGoldbach.U1446.fA_nonneg _ _ _ _ _ _,
          LeanLab.DensityGoldbach.U1446.fA_le_nuW (A i) (hA i) _ _ _ _ _⟩)
    rw [← LeanLab.DensityGoldbach.Smoothing408.scaled_norm]
    have heq : lpHat N (5 / 2) (fun x => (N : ℝ) * fv i x) =
        lpHat N (5 / 2) (fun x => fA (A i) (primorial z) (bp i) ((2 * n - 1) / 3) N x) := by
      congr 1
      funext x
      rw [hfvapp]
      field_simp
    rw [heq]
    exact le_trans h1 (le_max_left _ _)
  -- apply the transference principle at the residue `x₀`
  have hconv0 := hH1 N hNp (le_trans hNHK hNK) ν fv hbound hmassGe
    (by simpa only [Fin.sum_univ_three] using htotGe) hfourier hnorm
  set x₀ : ZMod N := ((n : ZMod N) - ((bp 0 + bp 1 + bp 2 : ℕ) : ZMod N)) /
    (primorial z : ZMod N) with hxdef
  have hWne : (primorial z : ZMod N) ≠ 0 := by
    intro h0
    have hval : (primorial z) % N = 0 := by
      have := congrArg ZMod.val h0
      simpa only [ZMod.val_natCast, ZMod.val_zero] using this
    exact hNdvd (Nat.dvd_of_mod_eq_zero hval)
  have hx₀ : (primorial z : ZMod N) * x₀ =
      (n : ZMod N) - ((bp 0 + bp 1 + bp 2 : ℕ) : ZMod N) := by
    rw [hxdef]
    field_simp
  have hconvx := hconv0 x₀
  have hcN : 0 < c / (N : ℝ) := by positivity
  have hexY : ∃ y : ZMod N, 0 < ∑ z : ZMod N, fv 0 y * fv 1 z * fv 2 (x₀ - y - z) := by
    by_contra hcon
    push_neg at hcon
    have hle : ∑ y : ZMod N, ∑ z : ZMod N, fv 0 y * fv 1 z * fv 2 (x₀ - y - z) ≤ 0 :=
      Finset.sum_nonpos fun y _ => hcon y
    linarith
  obtain ⟨y0, hy0⟩ := hexY
  have hexZ : ∃ z : ZMod N, 0 < fv 0 y0 * fv 1 z * fv 2 (x₀ - y0 - z) := by
    by_contra hcon
    push_neg at hcon
    have hle : ∑ z : ZMod N, fv 0 y0 * fv 1 z * fv 2 (x₀ - y0 - z) ≤ 0 :=
      Finset.sum_nonpos fun z _ => hcon z
    linarith
  obtain ⟨z0, hz0⟩ := hexZ
  set w0 : ZMod N := x₀ - y0 - z0 with hwdef
  have hwval : fv 2 (x₀ - y0 - z0) = fv 2 w0 := by rw [hwdef]
  rw [hwval] at hz0
  have hf0 : 0 < fv 0 y0 :=
    pos_of_mul_pos_left (pos_of_mul_pos_left hz0 (hbound 2 w0).1) (hbound 1 z0).1
  have hf1 : 0 < fv 1 z0 :=
    pos_of_mul_pos_right (pos_of_mul_pos_left hz0 (hbound 2 w0).1) (hbound 0 y0).1
  have hf2 : 0 < fv 2 w0 := pos_of_mul_pos_right hz0 (mul_pos hf0 hf1).le
  have hfa : ∀ i (x : ZMod N), 0 < fv i x → 0 < fA (A i) (primorial z) (bp i) ((2 * n - 1) / 3) N x := by
    intro i x h
    rw [hfvapp i x] at h
    rcases div_pos_iff.1 h with h' | h'
    · exact h'.1
    · linarith [h'.2]
  have hm0 := fA_pos_of_pos (x := y0) (hfa 0 y0 hf0)
  have hm1 := fA_pos_of_pos (x := z0) (hfa 1 z0 hf1)
  have hm2 := fA_pos_of_pos (x := w0) (hfa 2 w0 hf2)
  -- the triple and its congruence
  have hsum' : y0 + z0 + w0 = (x₀.val : ZMod N) := by
    rw [ZMod.natCast_zmod_val]
    simp only [hwdef]
    abel
  have hcast := three_sum_cast (primorial z) (bp 0) (bp 1) (bp 2) x₀.val y0 z0 w0 hsum'
  have hcast2 : (((primorial z * x₀.val + (bp 0 + bp 1 + bp 2) : ℕ)) : ZMod N) = (n : ZMod N) := by
    push_cast
    rw [ZMod.natCast_zmod_val, hx₀]
    push_cast
    ring
  have hcongN : ((primorial z * y0.val + bp 0) + (primorial z * z0.val + bp 1) +
      (primorial z * w0.val + bp 2)) ≡ n [MOD N] := by
    refine ZMod.natCast_eq_natCast_iff _ _ N |>.1 ?_
    exact hcast.trans hcast2
  have hcongW : ((primorial z * y0.val + bp 0) + (primorial z * z0.val + bp 1) +
      (primorial z * w0.val + bp 2)) ≡ n [MOD primorial z] := by
    have h1 := three_sum_modW (primorial z) (bp 0) (bp 1) (bp 2) y0 z0 w0
    have h2 : (bp 0 + bp 1 + bp 2) ≡ n [MOD primorial z] := by
      simpa only [hbpdef] using oddRep_sum_modW hz3 hW2m hodd (bb 0) (bb 1) (bb 2) hnb'
    exact h1.trans h2
  have hcong : ((primorial z * y0.val + bp 0) + (primorial z * z0.val + bp 1) +
      (primorial z * w0.val + bp 2)) ≡ n [MOD primorial z * N] :=
    (Nat.modEq_and_modEq_iff_modEq_mul hcopWN).1 ⟨hcongW, hcongN⟩
  -- conclude
  have hp0pos : 0 < primorial z * y0.val + bp 0 := (hA 0 hm0.1).pos
  refine IsSum3_of_congruent hnWN ?_ hm0.2 hm1.2 hm2.2 hm0.1 hm1.1 hm2.1 hp0pos hcong
  have h3 : 3 * ((2 * n - 1) / 3) ≤ 2 * n - 1 := Nat.mul_div_le _ _
  omega

end Lifting408b

/-- LEAF. Li and Pan math/0701240v3 pages 8 to 12, Sections 3 and 4,
and Shao pages 16 to 17 after equation 30. The three set version of the
explicit profile lifting. All three mass margins and Fourier bounds enter
AlsetriProp41 separately. There is no lower density assumption. -/
theorem weighted_lifting_mixed (H : AlsetriProp41) (R : U1488.Green66p (5 / 2))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ z₀ : ℕ, 3 ≤ z₀ ∧ ∀ z : ℕ, z₀ ≤ z → ∀ A : Fin 3 → Set ℕ, (∀ i, A i ⊆ P) →
      ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Odd n → ∀ m : ℕ, ∀ [NeZero m],
        m = primorial z / 2 → ∀ b₁ ∈ unitsMod m, ∀ b₂ ∈ unitsMod m, ∀ b₃ ∈ unitsMod m,
        (n : ZMod m) = b₁ + b₂ + b₃ →
        0 < Profiles408.halfProfile (A 0) z n δ m b₁ →
        0 < Profiles408.halfProfile (A 1) z n δ m b₂ →
        0 < Profiles408.halfProfile (A 2) z n δ m b₃ →
        3 / 2 < Profiles408.halfProfile (A 0) z n δ m b₁ +
          Profiles408.halfProfile (A 1) z n δ m b₂ + Profiles408.halfProfile (A 2) z n δ m b₃ →
        IsSum3 (A 0) (A 1) (A 2) n := by
  exact weighted_lifting_mixed_proof H R δ hδ

/-- LEAF. Shao pages 16 to 17, after equation 30 through Lemmas 4.5 and 4.6.
Given the transference principle and the restriction estimate, an admissible
triple of explicit truncated residue weights lifts to an integer representation.
This has no lower density assumption. It is shared with Theorem 1.1. -/
theorem weighted_lifting (H : AlsetriProp41) (R : U1488.Green66p (5 / 2))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ z₀ : ℕ, 3 ≤ z₀ ∧ ∀ z : ℕ, z₀ ≤ z → ∀ A : Set ℕ, A ⊆ P →
      ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Odd n → ∀ m : ℕ, ∀ [NeZero m],
        m = primorial z / 2 → ∀ b₁ ∈ unitsMod m, ∀ b₂ ∈ unitsMod m, ∀ b₃ ∈ unitsMod m,
        (n : ZMod m) = b₁ + b₂ + b₃ →
        0 < Profiles408.halfProfile A z n δ m b₁ →
        0 < Profiles408.halfProfile A z n δ m b₂ →
        0 < Profiles408.halfProfile A z n δ m b₃ →
        3 / 2 < Profiles408.halfProfile A z n δ m b₁ +
          Profiles408.halfProfile A z n δ m b₂ + Profiles408.halfProfile A z n δ m b₃ →
        IsSum3 A A A n := by
  obtain ⟨z₀, hz₀, hLift⟩ := weighted_lifting_mixed H R δ hδ
  refine ⟨z₀, hz₀, ?_⟩
  intro z hz A hA
  exact hLift z hz (fun _ => A) (fun _ => hA)


/-- Exact original Shao Theorem 1.3 statement. The threshold on n is retained.
CONDITIONAL ON the cited supply leaves, including the transference decomposition. -/
theorem shao_1_3_decomposed : Shao13 := by
  intro δ hδ
  let d : ℝ := min δ (1 / 8)
  have hd : 0 < d := lt_min hδ (by norm_num)
  have hdδ : d ≤ δ := min_le_left _ _
  have hdsmall : d ≤ 1 / 8 := min_le_right _ _
  obtain ⟨z, hz, hLift⟩ := weighted_lifting Decomp408a.alsetri_prop_4_1_decomposed
    restriction_five_halves d hd
  refine ⟨primorial z, primorial_pos z, ?_⟩
  intro A hA h1 h2 hlocal
  obtain ⟨Np, hProfile⟩ := local_profile d hd hdsmall z hz A hA (by linarith) (by linarith)
    (fun b hb hc => hdδ.trans (hlocal b hb hc))
  obtain ⟨Nl, hNl⟩ := hLift z le_rfl A hA
  obtain ⟨hmpos, hmodd, hmsq, hm3⟩ := half_primorial_props hz
  let m := primorial z / 2
  have : NeZero m := ⟨hmpos.ne'⟩
  refine ⟨max Np Nl, ?_⟩
  intro n hn hnodd
  obtain ⟨hbound, hpositive, hα1, hα2⟩ := hProfile n (le_trans (le_max_left _ _) hn) m rfl
  obtain ⟨b₁, hb₁, b₂, hb₂, b₃, hb₃, he, hsum⟩ :=
    shao_prop16 m hmodd hmsq hm3 (Profiles408.halfProfile A z n d m) hα1 hα2 (n : ZMod m)
  exact hNl n (le_trans (le_max_right _ _) hn) hnodd m rfl b₁ hb₁ b₂ hb₂ b₃ hb₃ he
    (hpositive b₁ hb₁) (hpositive b₂ hb₂) (hpositive b₃ hb₃) hsum

end LeanLab.DensityGoldbach.Decomp408b

#print axioms LeanLab.DensityGoldbach.Decomp408b.shao_1_3_decomposed
