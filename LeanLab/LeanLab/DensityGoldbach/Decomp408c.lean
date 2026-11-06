/-
Shao Theorem 1.1 from the explicit residue profile and the shared lifting step.
Source: https://arxiv.org/abs/1206.6139v2 pages 15 to 17.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.DensityGoldbach.Decomp408b
import LeanLab.DensityGoldbach.Prop14Full

open Finset
open Filter
open scoped Classical

namespace LeanLab.DensityGoldbach.Decomp408c

/-- `#(A ∩ [1,N])` over `Icc` equals the same count over `range (N+1)`, for `A ⊆ P`. -/
private lemma card_range_of_subset_P (A : Set ℕ) (hA : A ⊆ P) (N : ℕ) :
    ((range (N + 1)).filter (· ∈ A)).card =
      ((Icc 1 N).filter (fun p => p ∈ A ∧ p.Prime)).card := by
  congr 1
  ext p
  simp only [mem_filter, mem_range, mem_Icc]
  constructor
  · rintro ⟨hpN, hpA⟩
    have hp := hA hpA
    exact ⟨⟨hp.one_lt.le, by omega⟩, hpA, hp⟩
  · rintro ⟨⟨_, hpN⟩, hpA, _⟩
    exact ⟨by omega, hpA⟩

/-- The prime count over `Icc` equals the count over `range (N+1)`. -/
private lemma card_range_prime (N : ℕ) :
    ((range (N + 1)).filter Nat.Prime).card = ((Icc 1 N).filter Nat.Prime).card := by
  congr 1
  ext p
  simp only [mem_filter, mem_range, mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h2.one_lt.le, by omega⟩, h2⟩
  · rintro ⟨⟨h1, _⟩, h2⟩
    exact ⟨by omega, h2⟩

/-- `relRatio` in `range` form. -/
private lemma relRatio_eq_range (A : Set ℕ) (hA : A ⊆ P) (N : ℕ) :
    relRatio A N = (((range (N + 1)).filter (· ∈ A)).card : ℝ) /
      (((range (N + 1)).filter Nat.Prime).card : ℝ) := by
  unfold relRatio
  rw [card_range_of_subset_P A hA N, card_range_prime N]

/-- `relRatio` never exceeds one. -/
private lemma relRatio_le_one (A : Set ℕ) (N : ℕ) : relRatio A N ≤ 1 := by
  unfold relRatio
  apply div_le_one_of_le₀
  · exact_mod_cast card_le_card (show
      ((Icc 1 N).filter (fun p => p ∈ A ∧ p.Prime)) ⊆ (Icc 1 N).filter Nat.Prime from
        fun p hp => mem_filter.mpr ⟨(mem_filter.mp hp).1, (mem_filter.mp hp).2.2⟩)
  · positivity

/-- `relRatio` is nonnegative. -/
private lemma relRatio_nonneg (A : Set ℕ) (N : ℕ) : 0 ≤ relRatio A N := by
  unfold relRatio
  positivity

/-- From a lower bound on the relative lower density to an eventual counting inequality. -/
private lemma density_eventually (A : Set ℕ) (hA : A ⊆ P) (c c' : ℝ) (hc' : c' < c)
    (h : c ≤ lowerDensity A) :
    ∀ᶠ N : ℕ in atTop,
      c' * (((range (N + 1)).filter Nat.Prime).card : ℝ) ≤
        (((range (N + 1)).filter (· ∈ A)).card : ℝ) := by
  have hbdd : (atTop : Filter ℕ).IsBoundedUnder (· ≥ ·) (relRatio A) :=
    isBoundedUnder_of_eventually_ge
      (Eventually.of_forall (fun (N : ℕ) => relRatio_nonneg A N))
  have hratio : ∀ᶠ N : ℕ in atTop, c' < relRatio A N :=
    eventually_lt_of_lt_liminf (lt_of_lt_of_le hc' h) hbdd
  filter_upwards [hratio, eventually_ge_atTop 2] with N hN hN2
  have hN := hN.le
  rw [relRatio_eq_range A hA N] at hN
  have hpos : (0 : ℝ) < ((range (N + 1)).filter Nat.Prime).card := by
    have : 0 < ((range (N + 1)).filter Nat.Prime).card := by
      apply card_pos.mpr
      exact ⟨2, mem_filter.mpr ⟨mem_range.mpr (by omega), Nat.prime_two⟩⟩
    exact_mod_cast this
  exact (le_div_iff₀ hpos).mp hN


/-! ## Prime sums in a fixed progression, from the lab's `ap_sum_pow` -/

/-- Splitting a finite set of naturals at `N^(1-δ)`.  Same proof as
`LeanLab.DensityGoldbach.AlsetriShaoSharp.card_log_split`, repeated here so that no new
import is needed. -/
private lemma card_log_split (P : Finset ℕ) (N : ℕ) (hN : 1 ≤ N) (δ : ℝ) (hδ : δ < 1) :
    (1 - δ) * Real.log N * (P.card : ℝ) ≤
      (1 - δ) * Real.log N * ((N : ℝ) ^ (1 - δ) + 1) + ∑ p ∈ P, Real.log p := by
  set t : ℝ := (N : ℝ) ^ (1 - δ) with ht
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have ht0 : 0 < t := Real.rpow_pos_of_pos hN0 _
  have hlogt : Real.log t = (1 - δ) * Real.log N := Real.log_rpow hN0 _
  have h1δ : 0 < 1 - δ := by linarith
  set Ps := P.filter (fun p : ℕ => (p : ℝ) < t)
  set Pb := P.filter (fun p : ℕ => ¬ (p : ℝ) < t)
  have hcard : (P.card : ℝ) = Ps.card + Pb.card := by
    rw [← card_filter_add_card_filter_not (s := P) (fun p : ℕ => (p : ℝ) < t)]; push_cast; rfl
  have hsmall : (Ps.card : ℝ) ≤ t + 1 := by
    have h2 : Ps.card ≤ ⌈t⌉₊ := by
      calc Ps.card ≤ (range ⌈t⌉₊).card := by
            refine card_le_card fun p hp => ?_
            exact mem_range.2 (Nat.lt_ceil.2 (mem_filter.1 hp).2)
        _ = ⌈t⌉₊ := card_range _
    exact le_trans (by exact_mod_cast h2) (Nat.ceil_lt_add_one ht0.le).le
  have hbig : (1 - δ) * Real.log N * Pb.card ≤ ∑ p ∈ P, Real.log p := by
    have e : (1 - δ) * Real.log N * Pb.card = ∑ _p ∈ Pb, (1 - δ) * Real.log N := by
      rw [sum_const, nsmul_eq_mul]; ring
    rw [e]
    refine le_trans (sum_le_sum fun p hp => ?_) (sum_le_sum_of_subset_of_nonneg
      (filter_subset _ P) fun p _ _ => Real.log_natCast_nonneg p)
    have htp : t ≤ p := not_lt.1 (mem_filter.1 hp).2
    exact hlogt ▸ Real.log_le_log ht0 htp
  have hA : 0 ≤ (1 - δ) * Real.log N := mul_nonneg h1δ.le hL
  have := mul_le_mul_of_nonneg_left hsmall hA
  rw [hcard]
  nlinarith

/-- PNT in progressions, in relative form: the log-sum over one reduced residue differs from
`n / φ(d)` by at most a relative `ε`. -/
private lemma theta_ap_relative (d : ℕ) (hd : 1 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ a : ℕ, Nat.Coprime a d →
      |(∑ p ∈ (range (n + 1)).filter (fun p => p.Prime ∧ p % d = a % d), Real.log p) -
        (n : ℝ) / (Nat.totient d : ℝ)| ≤ ε * ((n : ℝ) / (Nat.totient d : ℝ)) := by
  have hφ : (0 : ℝ) < (Nat.totient d : ℝ) := by
    have h : 0 < Nat.totient d := Nat.totient_pos.mpr (by omega)
    exact_mod_cast h
  obtain ⟨n₀, hn₀⟩ :=
    LeanLab.HardyLittlewood1923.ap_sum_pow 0 d hd (ε / (Nat.totient d : ℝ)) (by positivity)
  refine ⟨n₀, fun n hn a ha => ?_⟩
  have h := hn₀ n hn a ha
  have hsum : (∑ p ∈ (range (n + 1)).filter (fun p => p.Prime ∧ p % d = a % d),
      Real.log (p : ℝ) * ((n : ℝ) - p) ^ 0) =
      ∑ p ∈ (range (n + 1)).filter (fun p => p.Prime ∧ p % d = a % d), Real.log (p : ℝ) := by
    apply sum_congr rfl
    intro p _
    rw [pow_zero, mul_one]
  have e1 : (n : ℝ) ^ (0 + 1) / ((↑(0 : ℕ) + 1) * (Nat.totient d : ℝ)) =
      (n : ℝ) / (Nat.totient d : ℝ) := by
    rw [pow_one]
    norm_num
  have e2 : ε / (Nat.totient d : ℝ) * (n : ℝ) ^ (0 + 1) =
      ε * ((n : ℝ) / (Nat.totient d : ℝ)) := by
    rw [pow_one, div_eq_mul_inv, div_eq_mul_inv]
    ring
  rw [hsum, e1, e2] at h
  exact h

/-- Chebyshev-type upper bound for `θ` from PNT with `d = 1`. -/
private lemma theta_upper_one (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (∑ p ∈ (range (n + 1)).filter Nat.Prime, Real.log p) ≤ (1 + ε) * n := by
  obtain ⟨n₀, hn₀⟩ := theta_ap_relative 1 le_rfl ε hε
  refine ⟨n₀, fun n hn => ?_⟩
  have h := hn₀ n hn 1 (by simp)
  have hfil : ((range (n + 1)).filter (fun p => Nat.Prime p ∧ p % 1 = 1 % 1)) =
      ((range (n + 1)).filter Nat.Prime) := by
    apply Finset.filter_congr
    intro p _
    simp [Nat.mod_one]
  rw [hfil] at h
  simp only [Nat.totient_one, Nat.cast_one, div_one] at h
  rw [abs_le] at h
  linarith [h.2]

/-- Chebyshev-type upper bound for `π`: `π(x) log x ≤ (1+ε) x` eventually. -/
private lemma pi_log_upper (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ N₀ : ℕ, ∀ x : ℕ, N₀ ≤ x →
      (((range (x + 1)).filter Nat.Prime).card : ℝ) * Real.log x ≤ (1 + ε) * x := by
  set δ : ℝ := ε / 4 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hδ1 : δ < 1 := by rw [hδdef]; linarith
  set ε₁ : ℝ := ε / 8 with hε₁def
  have hε₁ : 0 < ε₁ := by rw [hε₁def]; linarith
  obtain ⟨nθ, hθ⟩ := theta_upper_one ε₁ hε₁
  obtain ⟨n₂, hn₂⟩ := eventually_atTop.1
    ((LeanLab.HardyLittlewood1923.eventually_log_le ε₁ δ hε₁ hδ).and (eventually_ge_atTop 2))
  refine ⟨max nθ n₂, fun x hx => ?_⟩
  obtain ⟨hl, hx2⟩ := hn₂ x (le_of_max_le_right hx)
  have hxθ := hθ x (le_of_max_le_left hx)
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hx1 : (1 : ℝ) < x := by exact_mod_cast (by omega : 1 < x)
  have hL : 0 < Real.log x := Real.log_pos hx1
  set L : ℝ := Real.log x with hLdef
  set t : ℝ := (x : ℝ) ^ (1 - δ) with htdef
  have ht0 : 0 ≤ t := Real.rpow_nonneg hx0.le _
  have htn : t * (x : ℝ) ^ δ = (x : ℝ) := by
    rw [htdef, ← Real.rpow_add hx0]
    rw [show (1 - δ) + δ = 1 by ring, Real.rpow_one]
  have hLt : L * t ≤ ε₁ * x := by
    have h1 : L * t ≤ (ε₁ * (x : ℝ) ^ δ) * t := by
      apply mul_le_mul_of_nonneg_right _ ht0
      simpa only [hLdef] using hl
    calc L * t ≤ (ε₁ * (x : ℝ) ^ δ) * t := h1
      _ = ε₁ * x := by rw [mul_assoc, mul_comm ((x : ℝ) ^ δ) t, htn]
  have hxδ1 : (x : ℝ) ^ δ ≤ (x : ℝ) := by
    calc (x : ℝ) ^ δ ≤ (x : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1.le hδ1.le
      _ = (x : ℝ) := Real.rpow_one _
  have hL1 : L ≤ ε₁ * x := by
    have h2 : L ≤ ε₁ * (x : ℝ) ^ δ := hl
    have := mul_le_mul_of_nonneg_left hxδ1 hε₁.le
    nlinarith [this, h2]
  have hsplit := card_log_split ((range (x + 1)).filter Nat.Prime) x (by omega) δ hδ1
  set π : ℝ := (((range (x + 1)).filter Nat.Prime).card : ℝ) with hπdef
  have hLpos : 0 ≤ L := hL.le
  have hπpos : 0 ≤ π := by positivity
  have h1 : (1 - δ) * L * π ≤ (1 - δ) * L * (t + 1) + (1 + ε₁) * x := by
    nlinarith [hsplit, hxθ]
  have h2 : (1 - δ) * (L * (t + 1)) ≤ (ε / 4) * x := by
    have h3 : L * (t + 1) ≤ (2 * ε₁) * x := by nlinarith [hLt, hL1]
    have h3' : L * (t + 1) ≤ (ε / 4) * x := by
      have : (2 * ε₁) * x = (ε / 4) * x := by rw [hε₁def]; ring
      linarith [h3, this.le, this.ge]
    have h4 : (1 - δ) ≤ 1 := by linarith
    have h5 : (0 : ℝ) ≤ L * (t + 1) := by positivity
    calc (1 - δ) * (L * (t + 1)) ≤ 1 * (L * (t + 1)) :=
          mul_le_mul_of_nonneg_right h4 h5
      _ = L * (t + 1) := one_mul _
      _ ≤ (ε / 4) * x := h3'
  have h1' : (1 - δ) * (L * (t + 1)) = (1 - δ) * L * (t + 1) := by ring
  have hmain : (1 - δ) * L * π ≤ (1 + (ε / 4) + ε₁) * (x : ℝ) := by linarith [h1, h2, h1']
  have hgap : (1 + (ε / 4) + ε₁) * (x : ℝ) ≤ (1 - δ) * ((1 + ε) * (x : ℝ)) := by
    have e : (1 + (ε / 4) + ε₁) * (x : ℝ) = (1 + 3 * ε / 8) * (x : ℝ) := by
      rw [hε₁def]; ring
    have hle : (1 + 3 * ε / 8) ≤ (1 - δ) * (1 + ε) := by
      rw [hδdef]; nlinarith [hε.le, hε1]
    calc (1 + (ε / 4) + ε₁) * (x : ℝ) = (1 + 3 * ε / 8) * (x : ℝ) := e
      _ ≤ ((1 - δ) * (1 + ε)) * (x : ℝ) := mul_le_mul_of_nonneg_right hle hx0.le
      _ = (1 - δ) * ((1 + ε) * (x : ℝ)) := by ring
  have hkey : (1 - δ) * (L * π) ≤ (1 - δ) * ((1 + ε) * (x : ℝ)) := by
    have e : (1 - δ) * (L * π) = (1 - δ) * L * π := by ring
    rw [e]; linarith [hmain, hgap]
  have h1δ : (0 : ℝ) < 1 - δ := by linarith
  have hfin : L * π ≤ (1 + ε) * (x : ℝ) := (mul_le_mul_iff_of_pos_left h1δ).mp hkey
  rw [hπdef] at hfin ⊢
  calc (((range (x + 1)).filter Nat.Prime).card : ℝ) * Real.log x
      = Real.log x * (((range (x + 1)).filter Nat.Prime).card : ℝ) := by ring
    _ ≤ (1 + ε) * (x : ℝ) := hfin


/-! ## The modulus `W = primorial z`, its half `m`, and the reduced residues -/

private lemma two_dvd_primorial {z : ℕ} (hz : 2 ≤ z) : 2 ∣ primorial z :=
  Finset.dvd_prod_of_mem (fun p : ℕ => p)
    (mem_filter.mpr ⟨mem_range.mpr (by omega), Nat.prime_two⟩)

private lemma primorial_eq_two_mul {z m : ℕ} (hz : 2 ≤ z) (hm : m = primorial z / 2) :
    primorial z = 2 * m := by
  have h := two_dvd_primorial hz
  omega

private lemma totient_half {z m : ℕ} (hz : 2 ≤ z) (hm : m = primorial z / 2) (hodd : Odd m) :
    m.totient = (primorial z).totient := by
  rw [primorial_eq_two_mul hz hm, Nat.totient_mul (Nat.coprime_two_left.mpr hodd),
    Nat.totient_two, one_mul]

private lemma totient_primorial_pos (z : ℕ) : (0 : ℝ) < ((primorial z).totient : ℝ) := by
  have h : 0 < (primorial z).totient := Nat.totient_pos.mpr (primorial_pos z)
  exact_mod_cast h

/-- The reduced residues mod `m` number `φ(m)`. -/
private lemma card_unitsMod (m : ℕ) [NeZero m] : (unitsMod m).card = m.totient := by
  rw [Nat.totient_eq_card_coprime]
  refine Finset.card_bij (fun (b : ZMod m) _ => b.val) ?_ ?_ ?_
  · intro b hb
    have hu : IsUnit b := by
      simpa only [unitsMod, mem_filter, mem_univ, true_and] using hb
    have hc : Nat.Coprime b.val m := by
      have h : IsUnit ((b.val : ℕ) : ZMod m) := by rwa [ZMod.natCast_zmod_val]
      exact (ZMod.isUnit_iff_coprime b.val m).mp h
    exact mem_filter.mpr ⟨mem_range.mpr b.val_lt, hc.symm⟩
  · intro b1 _ b2 _ h
    exact ZMod.val_injective m h
  · intro a ha
    obtain ⟨ha1, ha2⟩ := mem_filter.mp ha
    have ham : a < m := mem_range.mp ha1
    refine ⟨(a : ZMod m), ?_, ?_⟩
    · simp only [unitsMod, mem_filter, mem_univ, true_and]
      exact (ZMod.isUnit_iff_coprime a m).mpr ha2.symm
    · exact ZMod.val_cast_of_lt ham

/-- The representative is determined by being odd, below `2m`, and reducing correctly. -/
private lemma oddRep_char {m : ℕ} [NeZero m] (hodd : Odd m) {b : ZMod m} {a : ℕ}
    (ha2 : a < 2 * m) (haodd : Odd a) (hamod : a % m = b.val) :
    Profiles408.oddRepresentative m b = a := by
  have hm0 : 0 < m := NeZero.pos m
  obtain ⟨hg2, hgodd, hgmod⟩ := Profiles408.oddRepresentative_properties m hodd b
  have hae : a = b.val + m * (a / m) := by
    have h := Nat.mod_add_div a m
    rw [hamod] at h
    omega
  have hge : Profiles408.oddRepresentative m b =
      b.val + m * (Profiles408.oddRepresentative m b / m) := by
    have h := Nat.mod_add_div (Profiles408.oddRepresentative m b) m
    rw [hgmod] at h
    omega
  have hadiv : a / m ≤ 1 := by
    have h : a / m < 2 := by rw [Nat.div_lt_iff_lt_mul hm0]; omega
    omega
  have hgdiv : Profiles408.oddRepresentative m b / m ≤ 1 := by
    have h : Profiles408.oddRepresentative m b / m < 2 := by
      rw [Nat.div_lt_iff_lt_mul hm0]; omega
    omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hadiv with hA | hA
  · rw [hA, Nat.mul_zero, add_zero] at hae
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hgdiv with hG | hG
    · rw [hG, Nat.mul_zero, add_zero] at hge
      omega
    · rw [hG, Nat.mul_one] at hge
      obtain ⟨k, hk⟩ := hgodd
      obtain ⟨j, hj⟩ := hodd
      obtain ⟨i, hi⟩ := haodd
      omega
  · rw [hA, Nat.mul_one] at hae
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hgdiv with hG | hG
    · rw [hG, Nat.mul_zero, add_zero] at hge
      obtain ⟨k, hk⟩ := hgodd
      obtain ⟨j, hj⟩ := hodd
      obtain ⟨i, hi⟩ := haodd
      omega
    · rw [hG, Nat.mul_one] at hge
      omega

/-- The representative of a unit `b` is coprime to `2m`. -/
private lemma oddRep_coprime {m : ℕ} [NeZero m] (hodd : Odd m) {b : ZMod m}
    (hb : b ∈ unitsMod m) : Nat.Coprime (Profiles408.oddRepresentative m b) (2 * m) := by
  have hu : IsUnit b := by
    simpa only [unitsMod, mem_filter, mem_univ, true_and] using hb
  have hc : Nat.Coprime b.val m := by
    have h : IsUnit ((b.val : ℕ) : ZMod m) := by rwa [ZMod.natCast_zmod_val]
    exact (ZMod.isUnit_iff_coprime b.val m).mp h
  obtain ⟨hg2, hgodd, hgmod⟩ := Profiles408.oddRepresentative_properties m hodd b
  have hgm : Nat.Coprime (Profiles408.oddRepresentative m b) m := by
    rw [Nat.coprime_iff_gcd_eq_one]
    calc Nat.gcd (Profiles408.oddRepresentative m b) m
        = Nat.gcd m (Profiles408.oddRepresentative m b) := Nat.gcd_comm _ _
      _ = Nat.gcd (Profiles408.oddRepresentative m b % m) m := Nat.gcd_rec m _
      _ = Nat.gcd b.val m := by rw [hgmod]
      _ = 1 := hc.gcd_eq_one
  have h2 : Nat.Coprime (Profiles408.oddRepresentative m b) 2 :=
    (Nat.coprime_two_left.mpr hgodd).symm
  have := hgm.mul_right h2
  rwa [mul_comm m 2] at this


/-- `log n / n → 0`, in the form needed below. -/
private lemma log_div_le_one (C : ℝ) (hC : 0 < C) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → C / n * Real.log n ≤ 1 := by
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (LeanLab.HardyLittlewood1923.eventually_log_le (1 / C) 1 (by positivity) one_pos)
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (le_trans (le_max_right _ _) hn : 1 ≤ n)
  have hl := hN n (le_trans (le_max_left _ _) hn)
  rw [Real.rpow_one] at hl
  have hn0 : (0 : ℝ) < n := by linarith
  have hstep : C / n * Real.log n ≤ C / n * (n / C) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc Real.log n ≤ 1 / C * n := hl
      _ = n / C := by ring
  have e : C / n * (n / C) = 1 := by
    field_simp
  linarith [hstep, e.le, e.ge]

/-- The representative of the residue of `p` is that residue, when `p` is an odd prime
coprime to `2m`. -/
private lemma oddRep_mod {m : ℕ} [NeZero m] (hodd : Odd m) {p : ℕ}
    (hp2 : Odd p) (_hp : Nat.Coprime p (2 * m)) :
    Profiles408.oddRepresentative m ((p % (2 * m) : ℕ) : ZMod m) = p % (2 * m) := by
  have hm0 : 0 < m := NeZero.pos m
  refine oddRep_char hodd ?_ ?_ ?_
  · exact Nat.mod_lt _ (by omega)
  · rw [Nat.odd_iff] at hp2 ⊢
    rw [Nat.mod_mod_of_dvd p (show 2 ∣ 2 * m from ⟨m, by ring⟩)]
    exact hp2
  · rw [ZMod.val_natCast]

/-- The filter defining the residue sum, rewritten with `3p < 2n` as `p ≤ (2n-1)/3`. -/
private lemma class_filter_eq (n : ℕ) (hn : 1 ≤ n) (A : Set ℕ) (W a : ℕ) :
    (range (n + 1)).filter (fun p => p ∈ A ∧ p % W = a % W ∧ 3 * p < 2 * n)
      = (range ((2 * n - 1) / 3 + 1)).filter (fun p => p ∈ A ∧ p % W = a % W) := by
  have hX1 : 3 * ((2 * n - 1) / 3) ≤ 2 * n - 1 := by
    have := Nat.div_mul_le_self (2 * n - 1) 3
    omega
  have hXn : (2 * n - 1) / 3 ≤ n := by
    have h : 2 * n - 1 ≤ 3 * n := by omega
    have := Nat.div_le_of_le_mul h
    omega
  ext p
  simp only [mem_filter, mem_range]
  constructor
  · rintro ⟨-, hA, hW, h3⟩
    have h3' : 3 * p ≤ 2 * n - 1 := by omega
    have hp : p ≤ (2 * n - 1) / 3 := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 3)]
      omega
    exact ⟨by omega, hA, hW⟩
  · rintro ⟨h1, hA, hW⟩
    have h1' : p ≤ (2 * n - 1) / 3 := by omega
    have h3 : 3 * p ≤ 2 * n - 1 := by
      calc 3 * p ≤ 3 * ((2 * n - 1) / 3) := Nat.mul_le_mul_left 3 h1'
        _ ≤ 2 * n - 1 := hX1
    exact ⟨by omega, hA, hW, by omega⟩


private lemma gcd_mod_right_eq (a W : ℕ) : Nat.gcd a W = Nat.gcd (a % W) W := by
  rw [Nat.gcd_comm a W, Nat.gcd_rec W a]

private lemma coprime_mod_iff (a W : ℕ) : Nat.Coprime (a % W) W ↔ Nat.Coprime a W := by
  have e : Nat.gcd (a % W) W = Nat.gcd a W := (gcd_mod_right_eq a W).symm
  rw [Nat.coprime_iff_gcd_eq_one, Nat.coprime_iff_gcd_eq_one, e]

/-- Cap `1` on every residue sum, uniformly in the residue, from PNT in progressions. -/
private lemma class_sum_le (A : Set ℕ) (hA : A ⊆ P) {z : ℕ} (hz : 3 ≤ z) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ a : ℕ,
      (3 * ((primorial z).totient : ℝ) / (2 * n)) *
        (∑ p ∈ (range (n + 1)).filter (fun p => p ∈ A ∧ p % primorial z = a % primorial z
          ∧ 3 * p < 2 * n), Real.log p) ≤ 1 + δ / 8 := by
  have hW1 : 1 ≤ primorial z := primorial_pos z
  have hφ : (0 : ℝ) < ((primorial z).totient : ℝ) := totient_primorial_pos z
  obtain ⟨n1, h1⟩ := theta_ap_relative (primorial z) hW1 (δ / 16) (by positivity)
  obtain ⟨n2, h2⟩ := log_div_le_one (3 * ((primorial z).totient : ℝ) * ((z : ℝ) + 1) / 2)
    (by positivity)
  obtain ⟨n3, h3⟩ := log_div_le_one (3 * ((primorial z).totient : ℝ) / 2) (by positivity)
  refine ⟨max (max n1 n2) (max n3 (2 * (n1 + 1))), fun n hn a => ?_⟩
  have hn1 : n1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : n2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn3 : n3 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn4 : 2 * (n1 + 1) ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hn1' : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hδne : δ ≠ 0 := ne_of_gt hδ
  set X : ℕ := (2 * n - 1) / 3 with hXdef
  have hXge : n1 ≤ X := by
    rw [hXdef, Nat.le_div_iff_mul_le (by norm_num : 0 < 3)]
    omega
  have hXn : X ≤ n := by
    rw [hXdef]
    have h : 2 * n - 1 ≤ 3 * n := by omega
    have := Nat.div_le_of_le_mul h
    omega
  have h3X : 3 * (X : ℝ) ≤ 2 * n := by
    have h := Nat.div_mul_le_self (2 * n - 1) 3
    have : (X : ℝ) = ((2 * n - 1) / 3 : ℕ) := rfl
    have h2' : 3 * X ≤ 2 * n - 1 := by omega
    have : (3 * X : ℕ) ≤ 2 * n := by omega
    exact_mod_cast this
  have hX1 : 1 ≤ X := by omega
  rw [class_filter_eq n hn1' A (primorial z) a]
  set s : Finset ℕ := (range (X + 1)).filter
    (fun p => p ∈ A ∧ p % primorial z = a % primorial z) with hs
  have hcoef : (0 : ℝ) ≤ 3 * ((primorial z).totient : ℝ) / (2 * n) := by positivity
  have hφne : ((primorial z).totient : ℝ) ≠ 0 := ne_of_gt hφ
  by_cases hc : Nat.Coprime a (primorial z)
  · have hsub : s ⊆ (range (X + 1)).filter
        (fun p => Nat.Prime p ∧ p % primorial z = a % primorial z) := by
      intro p hp
      obtain ⟨h1, h2, h3⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨h1, hA h2, h3⟩
    have hle : ∑ p ∈ s, Real.log p ≤ ∑ p ∈ (range (X + 1)).filter
        (fun p => Nat.Prime p ∧ p % primorial z = a % primorial z), Real.log p :=
      sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => Real.log_natCast_nonneg i)
    have hb := h1 X hXge a hc
    rw [abs_le] at hb
    have hXφ : (0 : ℝ) < (X : ℝ) / ((primorial z).totient : ℝ) := by positivity
    have hupper : ∑ p ∈ (range (X + 1)).filter
        (fun p => Nat.Prime p ∧ p % primorial z = a % primorial z), Real.log p
        ≤ (1 + δ / 16) * ((X : ℝ) / ((primorial z).totient : ℝ)) := by
      linarith [hb.2]
    have hmain := mul_le_mul_of_nonneg_left (hle.trans hupper) hcoef
    have hid : 3 * ((primorial z).totient : ℝ) / (2 * n) *
        ((1 + δ / 16) * ((X : ℝ) / ((primorial z).totient : ℝ))) =
        (1 + δ / 16) * (3 * (X : ℝ) / (2 * n)) := by
      field_simp
    rw [hid] at hmain
    have hratio : 3 * (X : ℝ) / (2 * n) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    nlinarith [hmain, hratio, hδ.le]
  · have hsubset : s ⊆ range (z + 1) := by
      intro p hp
      obtain ⟨-, hpA, hpW⟩ := mem_filter.mp hp
      have hpp : Nat.Prime p := hA hpA
      have hnc : ¬ Nat.Coprime p (primorial z) := by
        intro hco
        have hco' : Nat.Coprime (p % primorial z) (primorial z) :=
          (coprime_mod_iff p (primorial z)).mpr hco
        rw [hpW] at hco'
        exact hc ((coprime_mod_iff a (primorial z)).mp hco')
      have hdvd : p ∣ primorial z := by
        by_contra hnd
        exact hnc ((hpp.coprime_iff_not_dvd).mpr hnd)
      have := (hpp.dvd_primorial_iff).mp hdvd
      exact mem_range.mpr (by omega)
    have hcard : s.card ≤ z + 1 := by
      have := Finset.card_le_card hsubset
      simpa using this
    have hS : ∑ p ∈ s, Real.log p ≤ ((z : ℝ) + 1) * Real.log n := by
      have hstep : ∑ p ∈ s, Real.log p ≤ ∑ p ∈ s, Real.log n := by
        apply sum_le_sum
        intro p hp
        obtain ⟨hpr, -⟩ := mem_filter.mp hp
        have hpX : p ≤ X := by simpa using mem_range.mp hpr
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hA (mem_filter.mp hp).2.1).one_le
        have hple : (p : ℝ) ≤ n := by
          have : p ≤ n := by omega
          exact_mod_cast this
        exact Real.log_le_log (by linarith) hple
      have hconst : ∑ _p ∈ s, Real.log n = (s.card : ℝ) * Real.log n := by
        rw [sum_const, nsmul_eq_mul]
      have hLn : 0 ≤ Real.log n := Real.log_natCast_nonneg n
      rw [hconst] at hstep
      have : (s.card : ℝ) ≤ (z : ℝ) + 1 := by
        have : (s.card : ℝ) ≤ ((z + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
        push_cast at this
        linarith
      nlinarith [hstep, this, hLn]
    have hmain := mul_le_mul_of_nonneg_left hS hcoef
    have hid : 3 * ((primorial z).totient : ℝ) / (2 * n) * (((z : ℝ) + 1) * Real.log n) =
        3 * ((primorial z).totient : ℝ) * ((z : ℝ) + 1) / 2 / n * Real.log n := by
      field_simp
    rw [hid] at hmain
    have hb := h2 n (by omega)
    linarith [hmain, hb, hδ.le]


/-- The residue sums over the reduced residues add up to the sum over the primes of `A` that are
coprime to `2m`. -/
private lemma sum_classes (A : Set ℕ) (hA : A ⊆ P) {z m : ℕ} [NeZero m] (hz : 3 ≤ z)
    (hm : m = primorial z / 2) (hodd : Odd m) (Y : ℕ) :
    ∑ b ∈ unitsMod m, (∑ p ∈ (range (Y + 1)).filter
        (fun p => p ∈ A ∧ p % primorial z = (Profiles408.oddRepresentative m b) % primorial z),
        Real.log p)
      = ∑ p ∈ (range (Y + 1)).filter
        (fun p => p ∈ A ∧ Nat.Coprime p (primorial z)), Real.log p := by
  have hz2 : 2 ≤ z := by omega
  have hW2m : primorial z = 2 * m := primorial_eq_two_mul hz2 hm
  have hm0 : 0 < m := NeZero.pos m
  set F : Finset ℕ := (range (Y + 1)).filter (fun p => p ∈ A) with hFdef
  have hstep : ∀ b : ZMod m, (∑ p ∈ (range (Y + 1)).filter
      (fun p => p ∈ A ∧ p % primorial z = (Profiles408.oddRepresentative m b) % primorial z),
        Real.log p)
      = ∑ p ∈ F, (if p % primorial z = (Profiles408.oddRepresentative m b) % primorial z
          then Real.log p else 0) := by
    intro b
    have e : (range (Y + 1)).filter
        (fun p => p ∈ A ∧ p % primorial z = (Profiles408.oddRepresentative m b) % primorial z)
        = F.filter (fun p => p % primorial z =
            (Profiles408.oddRepresentative m b) % primorial z) := by
      rw [hFdef, Finset.filter_filter]
    rw [e, Finset.sum_filter]
  simp only [hstep]
  rw [Finset.sum_comm]
  have hrhs : ∑ p ∈ (range (Y + 1)).filter
      (fun p => p ∈ A ∧ Nat.Coprime p (primorial z)), Real.log p
      = ∑ p ∈ F, (if Nat.Coprime p (primorial z) then Real.log p else 0) := by
    have e : (range (Y + 1)).filter (fun p => p ∈ A ∧ Nat.Coprime p (primorial z))
        = F.filter (fun p => Nat.Coprime p (primorial z)) := by
      rw [hFdef, Finset.filter_filter]
    rw [e, Finset.sum_filter]
  rw [hrhs]
  apply Finset.sum_congr rfl
  intro p hpF
  have hpA : p ∈ A := (mem_filter.mp hpF).2
  have hpprime : Nat.Prime p := hA hpA
  by_cases hpc : Nat.Coprime p (primorial z)
  · rw [if_pos hpc]
    -- the unique matching residue
    have hpodd : Odd p := by
      rcases hpprime.eq_two_or_odd with h | h
      · exfalso
        rw [h] at hpc
        have hdvd : 2 ∣ primorial z := two_dvd_primorial hz2
        have := Nat.Coprime.eq_one_of_dvd hpc hdvd
        omega
      · rwa [Nat.odd_iff]
    have hcop2m : Nat.Coprime p (2 * m) := by rw [← hW2m]; exact hpc
    set b₀ : ZMod m := ((p % primorial z : ℕ) : ZMod m) with hb₀def
    have hb₀mem : b₀ ∈ unitsMod m := by
      simp only [unitsMod, mem_filter, mem_univ, true_and, hb₀def]
      have hcW : Nat.Coprime (p % primorial z) (primorial z) :=
        (coprime_mod_iff p (primorial z)).mpr hpc
      have hc2m : Nat.Coprime (p % primorial z) (2 * m) := by rw [← hW2m]; exact hcW
      have hcm : Nat.Coprime (p % primorial z) m :=
        hc2m.coprime_dvd_right (⟨2, by ring⟩ : m ∣ 2 * m)
      exact (ZMod.isUnit_iff_coprime (p % primorial z) m).mpr hcm
    have hrep : Profiles408.oddRepresentative m b₀ = p % primorial z := by
      rw [hb₀def, hW2m]
      exact oddRep_mod hodd hpodd hcop2m
    have huniq : ∀ b ∈ unitsMod m, b ≠ b₀ →
        (if p % primorial z = (Profiles408.oddRepresentative m b) % primorial z
          then Real.log p else 0) = 0 := by
      intro b _ hbne
      have hbv : b.val = (Profiles408.oddRepresentative m b) % m :=
        ((Profiles408.oddRepresentative_properties m hodd b).2.2).symm
      have hb₀v : b₀.val = (p % primorial z) % m := by
        rw [hb₀def]
        exact ZMod.val_natCast m (p % primorial z)
      have hne : (Profiles408.oddRepresentative m b) % primorial z ≠ p % primorial z := by
        intro he
        have hmW : m ∣ primorial z := ⟨2, by omega⟩
        have hcalc : (Profiles408.oddRepresentative m b) % m = (p % primorial z) % m := by
          calc (Profiles408.oddRepresentative m b) % m
              = (Profiles408.oddRepresentative m b % primorial z) % m :=
                  (Nat.mod_mod_of_dvd _ hmW).symm
            _ = (p % primorial z) % m := by rw [he]
        refine hbne (ZMod.val_injective m ?_)
        rw [hbv, hb₀v]
        exact hcalc
      rw [if_neg (Ne.symm hne)]
    have hsingle := Finset.sum_eq_single b₀ huniq (by
      intro hnotin
      exact absurd hb₀mem hnotin)
    rw [hsingle]
    rw [if_pos (by rw [hrep, Nat.mod_mod])]
  · rw [if_neg hpc]
    have hzero : ∀ b ∈ unitsMod m,
        (if p % primorial z = (Profiles408.oddRepresentative m b) % primorial z
          then Real.log p else 0) = (0 : ℝ) := by
      intro b hb
      have hcb : Nat.Coprime (Profiles408.oddRepresentative m b) (primorial z) := by
        rw [hW2m]
        exact oddRep_coprime hodd hb
      rw [if_neg]
      intro h
      exact hpc ((coprime_mod_iff p (primorial z)).mp (by
        rw [h]
        exact (coprime_mod_iff (Profiles408.oddRepresentative m b) (primorial z)).mpr hcb))
    calc ∑ b ∈ unitsMod m, (if p % primorial z =
          (Profiles408.oddRepresentative m b) % primorial z then Real.log p else 0)
        = ∑ b ∈ unitsMod m, (0 : ℝ) := Finset.sum_congr rfl hzero
      _ = 0 := by simp


/-- Lower Chebyshev bound for `θ` from PNT with `d = 1`. -/
private lemma theta_lower_one (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (1 - ε) * n ≤ (∑ p ∈ (range (n + 1)).filter Nat.Prime, Real.log p) := by
  obtain ⟨n₀, hn₀⟩ := theta_ap_relative 1 le_rfl ε hε
  refine ⟨n₀, fun n hn => ?_⟩
  have h := hn₀ n hn 1 (by simp)
  have hfil : ((range (n + 1)).filter (fun p => Nat.Prime p ∧ p % 1 = 1 % 1)) =
      ((range (n + 1)).filter Nat.Prime) := by
    apply Finset.filter_congr
    intro p _
    simp [Nat.mod_one]
  rw [hfil] at h
  simp only [Nat.totient_one, Nat.cast_one, div_one] at h
  rw [abs_le] at h
  linarith [h.1]

/-- The log-sum of `A` below `X = (2n-1)/3` is asymptotically `(5/8+δ/2)X`. -/
private lemma theta_A_lower (A : Set ℕ) (hA : A ⊆ P) {δ : ℝ} (hδ : 0 < δ) (hδ8 : δ ≤ 1 / 8)
    (hdensity : 5 / 8 + δ ≤ lowerDensity A) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (5 / 8 + δ / 2 - (11 / 8 - δ / 2) * (δ / 16)) * (((2 * n - 1) / 3 : ℕ) : ℝ) ≤
        ∑ p ∈ (range ((2 * n - 1) / 3 + 1)).filter (· ∈ A), Real.log p := by
  set γ : ℝ := δ / 16 with hγdef
  have hγ : 0 < γ := by rw [hγdef]; linarith
  have hγ1 : γ ≤ 1 := by rw [hγdef]; linarith
  have hδ3 : 0 ≤ 3 / 8 - δ / 2 := by linarith
  obtain ⟨n1, h1⟩ := theta_lower_one γ hγ
  obtain ⟨n2, h2⟩ := pi_log_upper γ hγ hγ1
  obtain ⟨n3, h3⟩ := eventually_atTop.1
    (density_eventually A hA (5 / 8 + δ) (5 / 8 + δ / 2) (by linarith) hdensity)
  refine ⟨max (max (2 * n1 + 2) (2 * n2 + 2)) (max (2 * n3 + 2) 8), fun n hn => ?_⟩
  have hn1b : 2 * n1 + 2 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2b : 2 * n2 + 2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn3b : 2 * n3 + 2 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn3' : 8 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  set X : ℕ := (2 * n - 1) / 3 with hXdef
  have hXn : X ≤ n := by
    rw [hXdef]
    have h : 2 * n - 1 ≤ 3 * n := by omega
    have := Nat.div_le_of_le_mul h
    omega
  have hX1 : n1 ≤ X := by
    have h3n1 : n1 * 3 ≤ 2 * n - 1 := by omega
    rw [hXdef]
    exact (Nat.le_div_iff_mul_le (k := 3) (by norm_num)).mpr h3n1
  have hX2 : n2 ≤ X := by
    have h3n2 : n2 * 3 ≤ 2 * n - 1 := by omega
    rw [hXdef]
    exact (Nat.le_div_iff_mul_le (k := 3) (by norm_num)).mpr h3n2
  have hX3 : n3 ≤ X := by
    have h3n3 : n3 * 3 ≤ 2 * n - 1 := by omega
    rw [hXdef]
    exact (Nat.le_div_iff_mul_le (k := 3) (by norm_num)).mpr h3n3
  set sP : Finset ℕ := (range (X + 1)).filter Nat.Prime with hsP
  set sA : Finset ℕ := (range (X + 1)).filter (· ∈ A) with hsA
  have hsub : sA ⊆ sP := by
    intro p hp
    have hpA : p ∈ A := (mem_filter.mp hp).2
    exact mem_filter.mpr ⟨(mem_filter.mp hp).1, hA hpA⟩
  have hsAeq : sP.filter (· ∈ A) = sA := by
    rw [hsA, hsP, Finset.filter_filter]
    apply Finset.filter_congr
    intro p _
    exact ⟨fun h => h.2, fun h => ⟨hA h, h⟩⟩
  have htheta : (1 - γ) * (X : ℝ) ≤ ∑ p ∈ sP, Real.log p := h1 X hX1
  have hcount : (5 / 8 + δ / 2) * (sP.card : ℝ) ≤ (sA.card : ℝ) := h3 X hX3
  have hpi : (sP.card : ℝ) * Real.log X ≤ (1 + γ) * (X : ℝ) := h2 X hX2
  have hX3' : 3 ≤ X := by
    have h9 : 3 * 3 ≤ 2 * n - 1 := by omega
    rw [hXdef]
    exact (Nat.le_div_iff_mul_le (k := 3) (by norm_num)).mpr h9
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hL : 0 < Real.log X := Real.log_pos (by
    have h1X : 1 < X := by omega
    exact_mod_cast h1X)
  have hsplit : ∑ p ∈ sA, Real.log p + ∑ p ∈ sP.filter (fun p => p ∉ A), Real.log p =
      ∑ p ∈ sP, Real.log p := by
    rw [← Finset.sum_filter_add_sum_filter_not sP (· ∈ A) (fun p => Real.log p), hsAeq]
  have hBcard : ((sP.filter (fun p => p ∉ A)).card : ℝ) = (sP.card : ℝ) - (sA.card : ℝ) := by
    have h := Finset.card_filter_add_card_filter_not (s := sP) (fun p => p ∈ A)
    rw [hsAeq] at h
    have hc : ((sA.card : ℝ) + ((sP.filter (fun p => p ∉ A)).card : ℝ)) = (sP.card : ℝ) := by
      exact_mod_cast h
    linarith
  have hBsum : ∑ p ∈ sP.filter (fun p => p ∉ A), Real.log p ≤
      ((3 / 8 - δ / 2) * (1 + γ)) * (X : ℝ) := by
    have hstep : ∑ p ∈ sP.filter (fun p => p ∉ A), Real.log p ≤
        ((sP.filter (fun p => p ∉ A)).card : ℝ) * Real.log X := by
      calc ∑ p ∈ sP.filter (fun p => p ∉ A), Real.log p
          ≤ ∑ _p ∈ sP.filter (fun p => p ∉ A), Real.log X := by
            apply sum_le_sum
            intro p hp
            have hpP : p ∈ sP := (mem_filter.mp hp).1
            have hpX : p ≤ X := by
              have := (mem_filter.mp hpP).1
              simpa using this
            have hp2 : 2 ≤ p := (mem_filter.mp hpP).2.two_le
            have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
            have hple : (p : ℝ) ≤ X := by exact_mod_cast hpX
            exact Real.log_le_log hp0 hple
        _ = ((sP.filter (fun p => p ∉ A)).card : ℝ) * Real.log X := by
            rw [sum_const, nsmul_eq_mul]
    have hcardle : ((sP.filter (fun p => p ∉ A)).card : ℝ) ≤
        (3 / 8 - δ / 2) * (sP.card : ℝ) := by
      rw [hBcard]
      nlinarith [hcount]
    have hcardnn : (0 : ℝ) ≤ (sP.filter (fun p => p ∉ A)).card := by positivity
    have hcle : ((sP.filter (fun p => p ∉ A)).card : ℝ) * Real.log X ≤
        ((3 / 8 - δ / 2) * (sP.card : ℝ)) * Real.log X :=
      mul_le_mul_of_nonneg_right hcardle hL.le
    have hfin : ((3 / 8 - δ / 2) * (sP.card : ℝ)) * Real.log X ≤
        (3 / 8 - δ / 2) * ((1 + γ) * (X : ℝ)) := by
      have := mul_le_mul_of_nonneg_left hpi hδ3
      nlinarith [this]
    linarith [hstep, hcle, hfin]
  have hK : (5 / 8 + δ / 2 - (11 / 8 - δ / 2) * (δ / 16)) * (X : ℝ) =
      ((1 - γ) - (3 / 8 - δ / 2) * (1 + γ)) * (X : ℝ) := by
    rw [hγdef]
    ring_nf
  rw [hK]
  nlinarith [htheta, hBsum, hsplit, hδ3]


/-- The primes of `A` below `X` that are not coprime to `primorial z` contribute at most
`(z+1) log X`. -/
private lemma junk_le (A : Set ℕ) (hA : A ⊆ P) {z : ℕ} (X : ℕ) :
    ∑ p ∈ (range (X + 1)).filter
        (fun p => p ∈ A ∧ ¬ Nat.Coprime p (primorial z)), Real.log p
      ≤ ((z : ℝ) + 1) * Real.log X := by
  have hsubset : (range (X + 1)).filter (fun p => p ∈ A ∧ ¬ Nat.Coprime p (primorial z))
      ⊆ range (z + 1) := by
    intro p hp
    obtain ⟨-, hpA, hnc⟩ := mem_filter.mp hp
    have hpp : Nat.Prime p := hA hpA
    have hdvd : p ∣ primorial z := by
      by_contra hnd
      exact hnc ((hpp.coprime_iff_not_dvd).mpr hnd)
    have := (hpp.dvd_primorial_iff).mp hdvd
    exact mem_range.mpr (by omega)
  have hcard : ((range (X + 1)).filter
      (fun p => p ∈ A ∧ ¬ Nat.Coprime p (primorial z))).card ≤ z + 1 := by
    have := Finset.card_le_card hsubset
    simpa using this
  have hstep : ∑ p ∈ (range (X + 1)).filter
      (fun p => p ∈ A ∧ ¬ Nat.Coprime p (primorial z)), Real.log p
      ≤ ∑ _p ∈ (range (X + 1)).filter
        (fun p => p ∈ A ∧ ¬ Nat.Coprime p (primorial z)), Real.log X := by
    apply sum_le_sum
    intro p hp
    have hpX : p ≤ X := by
      have := (mem_filter.mp hp).1
      simpa using this
    have hp0 : (0 : ℝ) < p := by
      have := (hA (mem_filter.mp hp).2.1).pos
      exact_mod_cast this
    have hple : (p : ℝ) ≤ X := by exact_mod_cast hpX
    exact Real.log_le_log hp0 hple
  have hconst : ∑ _p ∈ (range (X + 1)).filter
      (fun p => p ∈ A ∧ ¬ Nat.Coprime p (primorial z)), Real.log X =
      (((range (X + 1)).filter
        (fun p => p ∈ A ∧ ¬ Nat.Coprime p (primorial z))).card : ℝ) * Real.log X := by
    rw [sum_const, nsmul_eq_mul]
  rw [hconst] at hstep
  have hLn : 0 ≤ Real.log X := Real.log_natCast_nonneg X
  have hcle : (((range (X + 1)).filter
      (fun p => p ∈ A ∧ ¬ Nat.Coprime p (primorial z))).card : ℝ) ≤ (z : ℝ) + 1 := by
    have h1 : (((range (X + 1)).filter
        (fun p => p ∈ A ∧ ¬ Nat.Coprime p (primorial z))).card : ℝ) ≤ ((z + 1 : ℕ) : ℝ) := by
      exact_mod_cast hcard
    push_cast at h1
    linarith
  nlinarith [hstep, hcle, hLn]

set_option maxHeartbeats 2000000 in
/-- The mass bound: the profile mass over the reduced residues exceeds `5/8 φ(m)`. -/
private lemma mass_lower (A : Set ℕ) (hA : A ⊆ P) {z m : ℕ} [NeZero m] (hz : 3 ≤ z)
    (hm : m = primorial z / 2) (hodd : Odd m) {δ : ℝ} (hδ : 0 < δ) (hδ8 : δ ≤ 1 / 8)
    (hdensity : 5 / 8 + δ ≤ lowerDensity A) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      5 / 8 * (m.totient : ℝ) <
        ∑ b ∈ unitsMod m, Profiles408.halfProfile A z n δ m b := by
  have hz2 : 2 ≤ z := by omega
  have hW2m : primorial z = 2 * m := primorial_eq_two_mul hz2 hm
  have hTm_eq : m.totient = (primorial z).totient := totient_half hz2 hm hodd
  have hTmpos : (0 : ℝ) < (m.totient : ℝ) := by
    rw [hTm_eq]; exact totient_primorial_pos z
  obtain ⟨Ncap, hcap⟩ := class_sum_le A hA hz hδ
  obtain ⟨Nth, hth⟩ := theta_A_lower A hA hδ hδ8 hdensity
  obtain ⟨Nlog, hlog⟩ := log_div_le_one ((3 * (z : ℝ) + 9) * 4 / δ) (by positivity)
  refine ⟨max (max Ncap Nth) (max Nlog 8), fun n hn => ?_⟩
  have hncap : Ncap ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnth : Nth ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnlog : Nlog ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn8 : 8 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hδne : δ ≠ 0 := ne_of_gt hδ
  set X : ℕ := (2 * n - 1) / 3 with hXdef
  have hX3 : 3 ≤ X := by
    have h9 : 3 * 3 ≤ 2 * n - 1 := by omega
    rw [hXdef]
    exact (Nat.le_div_iff_mul_le (k := 3) (by norm_num)).mpr h9
  have hX1 : 1 ≤ X := by omega
  have hXn : X ≤ n := by
    rw [hXdef]
    have h : 2 * n - 1 ≤ 3 * n := by omega
    have := Nat.div_le_of_le_mul h
    omega
  have h3Xle : 3 * X ≤ 2 * n - 1 := by
    rw [hXdef]
    have := Nat.div_mul_le_self (2 * n - 1) 3
    omega
  have h3Xge : 2 * n - 3 ≤ 3 * X := by
    have hdec : (2 * n - 1) % 3 + 3 * X = 2 * n - 1 := by
      rw [hXdef]
      exact Nat.mod_add_div (2 * n - 1) 3
    have := Nat.mod_lt (2 * n - 1) (by norm_num : 0 < 3)
    omega
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hL : 0 < Real.log X := Real.log_pos (by
    have h1X : 1 < X := by omega
    exact_mod_cast h1X)
  set Tm : ℝ := (m.totient : ℝ) with hTmdef
  set Cf : ℝ := 3 * Tm / (2 * n) with hCfdef
  have hCf0 : 0 < Cf := by rw [hCfdef]; positivity
  set T : ℝ := ∑ p ∈ (range (X + 1)).filter
    (fun p => p ∈ A ∧ Nat.Coprime p (primorial z)), Real.log p with hTdef
  set θA : ℝ := ∑ p ∈ (range (X + 1)).filter (· ∈ A), Real.log p with hθAdef
  set J : ℝ := ∑ p ∈ (range (X + 1)).filter
    (fun p => p ∈ A ∧ ¬ Nat.Coprime p (primorial z)), Real.log p with hJdef
  -- the termwise lower bound
  have hterm : ∀ b ∈ unitsMod m, Cf *
      (∑ p ∈ (range (X + 1)).filter
        (fun p => p ∈ A ∧ p % primorial z = (Profiles408.oddRepresentative m b) % primorial z),
          Real.log p) - δ / 8 ≤ Profiles408.halfProfile A z n δ m b := by
    intro b _
    have hcf : (3 * ((primorial z).totient : ℝ) / (2 * n)) = Cf := by
      rw [hCfdef, hTmdef, hTm_eq]
    simp only [Profiles408.halfProfile, Profiles408.primeProfile]
    rw [class_filter_eq n hn1 A (primorial z) (Profiles408.oddRepresentative m b), ← hcf]
    exact le_max_left _ _
  have hsum_eq : ∑ b ∈ unitsMod m, (Cf *
      (∑ p ∈ (range (X + 1)).filter
        (fun p => p ∈ A ∧ p % primorial z = (Profiles408.oddRepresentative m b) % primorial z),
          Real.log p) - δ / 8)
      = Cf * T - δ / 8 * Tm := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
      sum_classes A hA hz hm hodd X, hTdef]
    rw [Finset.sum_const, card_unitsMod m, nsmul_eq_mul, hTmdef]
    ring
  have hjunk : J ≤ ((z : ℝ) + 1) * Real.log X := junk_le A hA X
  have hjunkn : J ≤ ((z : ℝ) + 1) * Real.log n := by
    have hLn1 : (1 : ℝ) ≤ Real.log n := by
      have h8n : (8 : ℝ) ≤ n := by exact_mod_cast hn8
      have h := Real.log_le_log (by norm_num : (0 : ℝ) < 8) h8n
      have h8 : Real.log 8 = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
        push_cast
        ring
      have h9 := Real.log_two_gt_d9
      rw [h8] at h
      linarith
    have hxnn : (X : ℝ) ≤ n := by exact_mod_cast hXn
    have := Real.log_le_log hXpos hxnn
    have hz1 : (0:ℝ) ≤ (z : ℝ) + 1 := by positivity
    nlinarith [hjunk, this, hz1]
  have hTJ : θA = T + J := by
    have hsp : ((range (X + 1)).filter (· ∈ A)) =
        (range (X + 1)).filter (fun p => p ∈ A ∧ Nat.Coprime p (primorial z)) ∪
        (range (X + 1)).filter (fun p => p ∈ A ∧ ¬ Nat.Coprime p (primorial z)) := by
      ext p
      simp only [mem_union, mem_filter]
      constructor
      · intro h
        obtain ⟨h1, h2⟩ := h
        by_cases hc : Nat.Coprime p (primorial z)
        · exact Or.inl ⟨h1, h2, hc⟩
        · exact Or.inr ⟨h1, h2, hc⟩
      · rintro (⟨h1, h2, -⟩ | ⟨h1, h2, -⟩) <;> exact ⟨h1, h2⟩
    have hdisj : Disjoint ((range (X + 1)).filter (fun p => p ∈ A ∧ Nat.Coprime p (primorial z)))
        ((range (X + 1)).filter (fun p => p ∈ A ∧ ¬ Nat.Coprime p (primorial z))) := by
      rw [Finset.disjoint_left]
      intro p hp hq
      exact (mem_filter.mp hq).2.2 (mem_filter.mp hp).2.2
    rw [hθAdef, hTdef, hJdef, hsp, Finset.sum_union hdisj]
  have hθ : (5 / 8 + δ / 2 - (11 / 8 - δ / 2) * (δ / 16)) * (X : ℝ) ≤ θA := hth n hnth
  -- the final arithmetic
  have hmass_ge : Cf * T - δ / 8 * Tm ≤
      ∑ b ∈ unitsMod m, Profiles408.halfProfile A z n δ m b := by
    rw [← hsum_eq]
    exact Finset.sum_le_sum hterm
  have hKdef : (5 / 8 + δ / 2 - (11 / 8 - δ / 2) * (δ / 16))
      = 5 / 8 + δ / 2 - (11 / 8 - δ / 2) * (δ / 16) := rfl
  have hKlow : (5 / 8 : ℝ) + δ / 8 + δ / 8 ≤
      5 / 8 + δ / 2 - (11 / 8 - δ / 2) * (δ / 16) := by
    nlinarith [hδ.le, hδ8]
  have hlogapp : (3 * (z : ℝ) + 6) * Real.log n / n ≤ δ / 4 := by
    have h0 : ((3 * (z : ℝ) + 9) * 4 / δ) / n * Real.log n ≤ 1 := hlog n hnlog
    have hmul := mul_le_mul_of_nonneg_right h0 (by positivity : (0 : ℝ) ≤ δ / 4)
    have e : ((3 * (z : ℝ) + 9) * 4 / δ) / n * Real.log n * (δ / 4)
        = (3 * (z : ℝ) + 9) * Real.log n / n := by
      field_simp
    rw [e] at hmul
    have hLn : (0 : ℝ) ≤ Real.log n := Real.log_natCast_nonneg n
    have hle : (3 * (z : ℝ) + 6) * Real.log n ≤ (3 * (z : ℝ) + 9) * Real.log n := by
      nlinarith [hLn]
    have hdiv : (3 * (z : ℝ) + 6) * Real.log n / n ≤ (3 * (z : ℝ) + 9) * Real.log n / n := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hle (by positivity)
    linarith [hdiv, hmul]
  have hG : (3 / (2 * n)) * ((5 / 8 + δ / 2 - (11 / 8 - δ / 2) * (δ / 16)) +
      ((z : ℝ) + 1) * Real.log n) ≤ δ / 8 := by
    have hLn : (0 : ℝ) ≤ Real.log n := Real.log_natCast_nonneg n
    have hb : (5 / 8 + δ / 2 - (11 / 8 - δ / 2) * (δ / 16)) ≤ 1 := by
      nlinarith [hδ.le, hδ8]
    have hnum : ((5 / 8 + δ / 2 - (11 / 8 - δ / 2) * (δ / 16)) +
        ((z : ℝ) + 1) * Real.log n) ≤ ((z : ℝ) + 2) * Real.log n := by
      have h1 : (1 : ℝ) ≤ Real.log n := by
        have h8n : (8 : ℝ) ≤ n := by exact_mod_cast hn8
        have hlog8 := Real.log_le_log (by norm_num : (0 : ℝ) < 8) h8n
        have h8 : Real.log 8 = 3 * Real.log 2 := by
          rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
          push_cast
          ring
        have h9 := Real.log_two_gt_d9
        rw [h8] at hlog8
        linarith
      nlinarith [hb, hLn, h1, hz]
    have h2n : (0 : ℝ) < 2 * n := by positivity
    have hstep : (3 / (2 * n)) * ((5 / 8 + δ / 2 - (11 / 8 - δ / 2) * (δ / 16)) +
        ((z : ℝ) + 1) * Real.log n) ≤ (3 / (2 * n)) * (((z : ℝ) + 2) * Real.log n) := by
      apply mul_le_mul_of_nonneg_left hnum (by positivity)
    have hfin : (3 / (2 * n)) * (((z : ℝ) + 2) * Real.log n) = (3 * (z : ℝ) + 6) * Real.log n / (2 * n) := by
      field_simp
      ring
    rw [hfin] at hstep
    have hhalf : (3 * (z : ℝ) + 6) * Real.log n / (2 * n) = ((3 * (z : ℝ) + 6) * Real.log n / n) / 2 := by
      field_simp
    rw [hhalf] at hstep
    linarith [hstep, hlogapp]
  -- the three comparisons
  have e1 : Cf * ((5 / 8 + δ / 2 - (11 / 8 - δ / 2) * (δ / 16)) * (X : ℝ)) - Cf * J ≤ Cf * T := by
    have hTJ' : T = θA - J := by linarith [hTJ]
    have : (5 / 8 + δ / 2 - (11 / 8 - δ / 2) * (δ / 16)) * (X : ℝ) - J ≤ T := by
      rw [hTJ']; linarith [hθ]
    nlinarith [mul_le_mul_of_nonneg_left this hCf0.le]
  have e2 : Cf * ((5 / 8 + δ / 2 - (11 / 8 - δ / 2) * (δ / 16)) * (X : ℝ))
      = Tm * ((5 / 8 + δ / 2 - (11 / 8 - δ / 2) * (δ / 16)) * (3 * (X : ℝ) / (2 * n))) := by
    rw [hCfdef]
    field_simp
  have e3 : (1 : ℝ) - 3 / (2 * n) ≤ 3 * (X : ℝ) / (2 * n) := by
    have hcast : (2 * n - 3 : ℕ) ≤ 3 * X := h3Xge
    have h1 : ((2 * n - 3 : ℕ) : ℝ) ≤ 3 * (X : ℝ) := by exact_mod_cast hcast
    have h2 : ((2 * n - 3 : ℕ) : ℝ) = 2 * (n : ℝ) - 3 := by
      push_cast [Nat.cast_sub (by omega : 3 ≤ 2 * n)]
      ring
    rw [h2] at h1
    rw [← sub_nonneg]
    have : 3 * (X : ℝ) / (2 * n) - (1 - 3 / (2 * n)) = (3 * (X : ℝ) + 3 - 2 * n) / (2 * n) := by
      field_simp
      ring
    rw [this]
    apply div_nonneg _ (by positivity)
    linarith
  have e4 : Cf * J ≤ Tm * ((3 / (2 * n)) * (((z : ℝ) + 1) * Real.log n)) := by
    have h := mul_le_mul_of_nonneg_left hjunkn hCf0.le
    have e : Cf * (((z : ℝ) + 1) * Real.log n) = Tm * ((3 / (2 * n)) * (((z : ℝ) + 1) * Real.log n)) := by
      rw [hCfdef]
      field_simp
    linarith [h, e.le, e.ge]
  have hKm : (0 : ℝ) ≤ 5 / 8 + δ / 2 - (11 / 8 - δ / 2) * (δ / 16) := by
    nlinarith [hδ.le, hδ8]
  -- assemble
  have hfinal : Tm * (5 / 8) < Tm * (5 / 8 + δ / 8) := by
    have : (0 : ℝ) < Tm * (δ / 8) := by positivity
    nlinarith
  have hbound : Tm * (5 / 8 + δ / 8) ≤ Cf * T - δ / 8 * Tm := by
    have hXnn : (0 : ℝ) ≤ 3 * (X : ℝ) / (2 * n) := by positivity
    have hK' : (1 - 3 / (2 * n)) * (5 / 8 + δ / 2 - (11 / 8 - δ / 2) * (δ / 16)) ≤
        3 * (X : ℝ) / (2 * n) * (5 / 8 + δ / 2 - (11 / 8 - δ / 2) * (δ / 16)) :=
      mul_le_mul_of_nonneg_right e3 hKm
    nlinarith [e1, e2, e4, hKlow, hG, hK', hKm, hXnn, hTmpos, hCf0]
  linarith [hmass_ge, hbound, hfinal]


/-- LEAF. Shao page 15, equation 28. PNT in progressions gives the cap 1
on every fixed reduced class. Global relative density above 5/8 gives a total
profile mass above 5/8 times phi of the modulus. There is no representation
conclusion and no transference input. -/
theorem global_profile (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 8)
    (z : ℕ) (hz : 3 ≤ z) (A : Set ℕ) (hA : A ⊆ P)
    (hdensity : 5 / 8 + δ ≤ lowerDensity A) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ m : ℕ, ∀ [NeZero m], m = primorial z / 2 →
      let f := Profiles408.halfProfile A z n δ m
      (∀ b, 0 ≤ f b ∧ f b ≤ 1) ∧
      5 / 8 * (m.totient : ℝ) < ∑ b ∈ unitsMod m, f b := by
  obtain ⟨hmpos, hmodd, hmsq, hm3⟩ := half_primorial_props hz
  have _ : NeZero (primorial z / 2) := ⟨hmpos.ne'⟩
  obtain ⟨Nmass, hmass⟩ := mass_lower A hA hz rfl hmodd hδ hδsmall hdensity
  obtain ⟨Ncap, hcap⟩ := class_sum_le A hA hz hδ
  refine ⟨max Ncap Nmass, fun n hn m inst hm => ?_⟩
  subst hm
  constructor
  · intro b
    constructor
    · simp only [Profiles408.halfProfile, Profiles408.primeProfile]
      exact le_max_right _ _
    · have hcapb := hcap n (le_trans (le_max_left _ _) hn)
        (Profiles408.oddRepresentative (primorial z / 2) b)
      simp only [Profiles408.halfProfile, Profiles408.primeProfile]
      apply max_le
      · linarith
      · norm_num
  · exact hmass n (le_trans (le_max_right _ _) hn)

/-- Shao page 16, equation 30. Nonnegative values with positive product
are individually positive. -/
theorem positive_factors (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hprod : 0 < a * b * c) : 0 < a ∧ 0 < b ∧ 0 < c := by
  have hab : 0 < a * b := pos_of_mul_pos_left hprod hc
  exact ⟨pos_of_mul_pos_left hab hb, pos_of_mul_pos_right hab ha,
    pos_of_mul_pos_right hprod (mul_nonneg ha hb)⟩

/-- Exact original Shao Theorem 1.1 statement.
CONDITIONAL ON the global profile and shared analytic supply leaves. -/
theorem shao_1_1_decomposed : Shao11 := by
  intro A hA hden
  let δ : ℝ := min ((lowerDensity A - 5 / 8) / 2) (1 / 8)
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδsmall : δ ≤ 1 / 8 := min_le_right _ _
  have hδden : 5 / 8 + δ ≤ lowerDensity A := by
    have := min_le_left ((lowerDensity A - 5 / 8) / 2) (1 / 8)
    linarith
  obtain ⟨z, hz, hLift⟩ := Decomp408b.weighted_lifting Decomp408a.alsetri_prop_4_1_decomposed
    Decomp408b.restriction_five_halves δ hδ
  obtain ⟨Np, hProfile⟩ := global_profile δ hδ hδsmall z hz A hA hδden
  obtain ⟨Nl, hNl⟩ := hLift z le_rfl A hA
  obtain ⟨hmpos, hmodd, hmsq, hm3⟩ := half_primorial_props hz
  let m := primorial z / 2
  have : NeZero m := ⟨hmpos.ne'⟩
  refine ⟨max Np Nl, ?_⟩
  intro n hn hnodd
  obtain ⟨hbound, hmass⟩ := hProfile n (le_trans (le_max_left _ _) hn) m rfl
  let f := Profiles408.halfProfile A z n δ m
  obtain ⟨b₁, hb₁, b₂, hb₂, b₃, hb₃, he, hp, hs⟩ :=
    prop_1_4_proved m hmodd hmsq f hbound hmass (n : ZMod m)
  obtain ⟨h1, h2, h3⟩ := positive_factors (f b₁) (f b₂) (f b₃)
    (hbound b₁).1 (hbound b₂).1 (hbound b₃).1 hp
  exact hNl n (le_trans (le_max_right _ _) hn) hnodd m rfl b₁ hb₁ b₂ hb₂ b₃ hb₃ he h1 h2 h3 hs

end LeanLab.DensityGoldbach.Decomp408c

#print axioms LeanLab.DensityGoldbach.Decomp408c.global_profile
#print axioms LeanLab.DensityGoldbach.Decomp408c.positive_factors
#print axioms LeanLab.DensityGoldbach.Decomp408c.shao_1_1_decomposed
