/-
Ported from Prove2Me, mission 0814790f.
Source Def_axler_theta_chain_base. Author recorded as None in the pulled header. Apache 2.0.
Lean 4.33.1 source adapted for Lean 4.35.0.
Certificate data use product tuples. Specifications are expanded in theorem types.
Derived certificates for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/

import LeanLab.Ported.Prove2Me.Def_axler_theta_prep

namespace LeanLab.Ported.Prove2Me.Task666

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Finset Real
namespace AxlerChain

open RosserBitSieve RosserSieveData RosserFastCompute RosserScan AxlerTheta

abbrev Blk := ℕ × ℕ × ℕ × ℕ × ℕ

abbrev Grp := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × List Blk

def gate : ℕ := 70111

def blkOK (gbase : ℕ) (m : ℕ) (B : Blk) (L U : ℕ) : Bool × ℕ × ℕ :=
  let len := B.2.1 - B.1
  forceNat (m / 2 ^ (B.1 - gbase) % 2 ^ len) fun w =>
  forceNat (bitCount (depthFor len) w) fun cnt =>
  if cnt = 0 then
    if B.1 < gate then (true, L, U)
    else forceNat (logUpNum B.2.1) fun lhi =>
      (decide (((B.2.1 * scale - L) * lhi ^ 4 < 100 * B.1 * scale ^ 5) ∧
        (U < B.1 * scale ∨ (U - B.1 * scale) * lhi ^ 4 < 100 * B.1 * scale ^ 5) ∧
        (B.1 = gate → (U - B.1 * scale) * (logUpNum B.1) ^ 4 < 100 * B.1 * scale ^ 5 ∧
          (B.1 * scale - L) * (logUpNum B.1) ^ 4 < 100 * B.1 * scale ^ 5)), L, U)
  else
    forceNat (logLoNum (B.1 + 1)) fun llo =>
    forceNat (logUpNum B.2.1) fun lhi =>
    forceNat (L + cnt * llo) fun L' =>
    forceNat (U + cnt * lhi) fun U' =>
    if B.1 < gate then (true, L', U')
    else
      (decide (
        (B.1 < B.2.2.1 ∧ B.2.2.1 ≤ B.2.1 ∧ w % 2 ^ (B.2.2.1 - B.1 - 1) = 0 ∧ w.testBit (B.2.2.1 - B.1 - 1) = true) ∧
        ((cnt < 2 ∧ B.2.2.2.1 = 0) ∨ (2 ≤ cnt ∧ B.2.2.1 < B.2.2.2.1 ∧ B.2.2.2.1 ≤ B.2.1 ∧ w.testBit (B.2.2.2.1 - B.1 - 1) = true)) ∧
        ((cnt < 3 ∧ B.2.2.2.2 = 0) ∨ (3 ≤ cnt ∧ B.2.2.2.1 < B.2.2.2.2 ∧ B.2.2.2.2 ≤ B.2.1 ∧ w.testBit (B.2.2.2.2 - B.1 - 1) = true)) ∧
        ((U + cnt * lhi < B.1 * scale) ∨ ((U + cnt * lhi - B.1 * scale) * lhi ^ 4 < 100 * B.1 * scale ^ 5)) ∧
        ((B.2.2.1 * scale - L) * lhi ^ 4 < 100 * B.1 * scale ^ 5) ∧
        (((if 2 ≤ cnt then B.2.2.2.1 else B.2.1) * scale - L - llo) * lhi ^ 4 < 100 * B.2.2.1 * scale ^ 5) ∧
        (cnt < 2 ∨ (((if 3 ≤ cnt then B.2.2.2.2 else B.2.1) * scale - L - 2 * llo) * lhi ^ 4 < 100 * B.2.2.2.1 * scale ^ 5)) ∧
        (cnt < 3 ∨ ((B.2.1 * scale - L - 3 * llo) * lhi ^ 4 < 100 * B.2.2.2.2 * scale ^ 5)) ∧
        (B.1 = gate → (U - B.1 * scale) * (logUpNum B.1) ^ 4 < 100 * B.1 * scale ^ 5 ∧
          (B.1 * scale - L) * (logUpNum B.1) ^ 4 < 100 * B.1 * scale ^ 5)
      ), L', U')

def grpGo (G : Grp) (gbase m : ℕ) : ℕ → ℕ → ℕ → List Blk → Bool
  | prev, L, U, [] => (prev = G.2.1) && (L = G.2.2.2.2.1) && (U = G.2.2.2.2.2.1)
  | prev, L, U, B :: rest =>
    match blkOK gbase m B L U with
    | (ok, L', U') => (prev = B.1) && ok && grpGo G gbase m B.2.1 L' U' rest

def grpOK (G : Grp) : Bool :=
  forceNat (mask G.1 G.2.1) fun m => grpGo G G.1 m G.1 G.2.2.1 G.2.2.2.1 G.2.2.2.2.2.2

end AxlerChain
-- ============================================================
-- Part 3: soundness of the chained block certificate
-- ============================================================

namespace AxlerChain

open Finset Real
open RosserBitSieve RosserSieveData RosserFastCompute RosserScan AxlerTheta

abbrev S : ℝ := (scale : ℝ)

theorem S_pos : 0 < S := by norm_num [S, scale]

theorem primesLE_sdiff_filter (a b : ℕ) :
    Nat.primesLE b \ Nat.primesLE a = (Nat.primesLE b).filter (fun p => a < p) := by
  ext p
  constructor
  · intro hp
    rw [Finset.mem_sdiff] at hp
    rw [Finset.mem_filter]
    exact ⟨hp.1, not_le.mp (fun hpa => hp.2 (Nat.mem_primesLE.mpr ⟨hpa, (Nat.mem_primesLE.mp hp.1).2⟩))⟩
  · intro hp
    rw [Finset.mem_filter] at hp
    rw [Finset.mem_sdiff]
    refine ⟨hp.1, fun h => ?_⟩
    exact absurd hp.2 (not_lt.mpr (Nat.mem_primesLE.mp h).1)

theorem theta_diff_eq {a b : ℕ} (hab : a ≤ b) :
    Chebyshev.theta (b : ℝ) - Chebyshev.theta (a : ℝ)
      = ∑ p ∈ (Nat.primesLE b).filter (fun p => a < p), Real.log (p : ℝ) := by
  have hsub : Nat.primesLE a ⊆ Nat.primesLE b := by
    intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨hp.1.trans hab, hp.2⟩
  rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log,
    ← primesLE_sdiff_filter a b]
  have h := Finset.sum_sdiff (s₁ := Nat.primesLE a) (s₂ := Nat.primesLE b) hsub
    (f := fun p => Real.log (p : ℝ))
  linarith

theorem theta_lo_card {a b : ℕ} (ha1 : 1 ≤ a) (hab : a < b) (hb64 : b < 2 ^ 64) :
    (((Nat.primesLE b).filter (fun p => a < p)).card : ℝ) * (logLoNum (a + 1) : ℝ)
      ≤ S * (Chebyshev.theta (b : ℝ) - Chebyshev.theta (a : ℝ)) := by
  have hconst : (((Nat.primesLE b).filter (fun p => a < p)).card : ℝ) * (logLoNum (a + 1) : ℝ)
      = ∑ _p ∈ (Nat.primesLE b).filter (fun p => a < p), (logLoNum (a + 1) : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [theta_diff_eq (le_of_lt hab), Finset.mul_sum, hconst]
  refine Finset.sum_le_sum (fun p hp => ?_)
  have hp' := Finset.mem_filter.mp hp
  have hpr : Nat.Prime p := (Nat.mem_primesLE.mp hp'.1).2
  have hap : a < p := hp'.2
  have h1 : (logLoNum (a + 1) : ℝ) ≤ (scale : ℝ) * Real.log ((a : ℝ) + 1) := by
    simpa using logLoNum_sound (a + 1) (by omega) (by omega)
  calc (logLoNum (a + 1) : ℝ) ≤ (scale : ℝ) * Real.log ((a : ℝ) + 1) := h1
    _ ≤ (scale : ℝ) * Real.log (p : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.log_le_log (by positivity) (by exact_mod_cast (show a + 1 ≤ p by omega))
    _ = S * Real.log (p : ℝ) := rfl

theorem theta_up_card {a b : ℕ} (ha1 : 1 ≤ a) (hab : a < b) (hb64 : b < 2 ^ 64) :
    S * (Chebyshev.theta (b : ℝ) - Chebyshev.theta (a : ℝ))
      ≤ (((Nat.primesLE b).filter (fun p => a < p)).card : ℝ) * (logUpNum b : ℝ) := by
  have hconst : ∑ _p ∈ (Nat.primesLE b).filter (fun p => a < p), (logUpNum b : ℝ)
      = (((Nat.primesLE b).filter (fun p => a < p)).card : ℝ) * (logUpNum b : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [theta_diff_eq (le_of_lt hab), Finset.mul_sum, ← hconst]
  refine Finset.sum_le_sum (fun p hp => ?_)
  have hp' := Finset.mem_filter.mp hp
  have hpb : p ≤ b := (Nat.mem_primesLE.mp hp'.1).1
  have hpr : Nat.Prime p := (Nat.mem_primesLE.mp hp'.1).2
  calc S * Real.log (p : ℝ) ≤ S * Real.log (b : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.log_le_log (by exact_mod_cast hpr.pos) (by exact_mod_cast hpb)
    _ ≤ (logUpNum b : ℝ) := logUpNum_sound b (by omega) hb64

theorem cast_check {D A lhin : ℕ} (h : D * lhin ^ 4 < 100 * A * scale ^ 5) :
    (D : ℝ) * (lhin : ℝ) ^ 4 < 100 * (A : ℝ) * S ^ 5 := by
  exact_mod_cast h

theorem abs_bound_of {x : ℝ} (hS : 0 < S)
    (hlo : S * x - 100 * S * x / (Real.log x) ^ 4 < S * Chebyshev.theta x)
    (hhi : S * Chebyshev.theta x < S * x + 100 * S * x / (Real.log x) ^ 4) :
    |Chebyshev.theta x - x| < 100 * x / (Real.log x) ^ 4 := by
  set t := 100 * x / (Real.log x) ^ 4 with ht
  have h1 : S * (x - t) < S * Chebyshev.theta x := by
    have he : 100 * S * x / (Real.log x) ^ 4 = S * t := by rw [ht]; ring
    rw [mul_sub, ← he]
    linarith
  have h2 : S * Chebyshev.theta x < S * (x + t) := by
    have he : 100 * S * x / (Real.log x) ^ 4 = S * t := by rw [ht]; ring
    rw [mul_add, ← he]
    linarith
  have hx1 := (mul_lt_mul_iff_of_pos_left hS).mp h1
  have hx2 := (mul_lt_mul_iff_of_pos_left hS).mp h2
  rw [abs_lt]
  constructor <;> linarith

theorem hi_step {x : ℝ} {A Un lhin : ℕ} (hx : 1 < x) (hAx : (A : ℝ) ≤ x)
    (hlhi : S * Real.log x ≤ (lhin : ℝ))
    (hchk : (Un : ℝ) < (A : ℝ) * S ∨
      (((Un - A * scale : ℕ) : ℝ) * (lhin : ℝ) ^ 4 < 100 * (A : ℝ) * S ^ 5)) :
    (Un : ℝ) < S * x + 100 * S * x / (Real.log x) ^ 4 := by
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hSpos : 0 < S := S_pos
  have htpos : 0 < 100 * S * x / (Real.log x) ^ 4 := by
    apply div_pos
    · positivity
    · exact pow_pos hlogx 4
  rcases hchk with hlt | hchk
  · have h1 : (Un : ℝ) < S * x := by nlinarith [hlt, hAx, hSpos]
    linarith
  · by_cases hAle : A * scale ≤ Un
    · have hcast : (((Un - A * scale : ℕ) : ℝ)) = (Un : ℝ) - (A : ℝ) * S := by
        rw [Nat.cast_sub hAle]
        push_cast
        ring
      rw [hcast] at hchk
      have hlhin_pos : (0 : ℝ) < (lhin : ℝ) ^ 4 := by
        have : (0 : ℝ) < (lhin : ℝ) := lt_of_lt_of_le (mul_pos hSpos hlogx) hlhi
        exact pow_pos this 4
      have hpow : (S * Real.log x) ^ 4 ≤ (lhin : ℝ) ^ 4 :=
        pow_le_pow_left₀ (mul_nonneg hSpos.le hlogx.le) hlhi 4
      have h1 : 100 * (A : ℝ) * S ^ 5 / (lhin : ℝ) ^ 4 ≤
          100 * (A : ℝ) * S ^ 5 / (S * Real.log x) ^ 4 :=
        div_le_div_of_nonneg_left (by positivity)
          (pow_pos (mul_pos hSpos hlogx) 4) hpow
      have h2 : 100 * (A : ℝ) * S ^ 5 / (S * Real.log x) ^ 4 =
          100 * (A : ℝ) * S / (Real.log x) ^ 4 := by
        rw [mul_pow]
        field_simp
      have h3 : 100 * (A : ℝ) * S / (Real.log x) ^ 4 ≤
          100 * S * x / (Real.log x) ^ 4 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [hAx, hSpos]
      have hUn : (Un : ℝ) - (A : ℝ) * S < 100 * (A : ℝ) * S ^ 5 / (lhin : ℝ) ^ 4 := by
        rw [lt_div_iff₀ hlhin_pos]
        linarith
      have hAlem : (A : ℝ) * S ≤ S * x := by nlinarith [hAx, hSpos]
      calc (Un : ℝ) < (A : ℝ) * S + 100 * (A : ℝ) * S ^ 5 / (lhin : ℝ) ^ 4 := by linarith
        _ ≤ (A : ℝ) * S + 100 * S * x / (Real.log x) ^ 4 := by linarith
        _ ≤ S * x + 100 * S * x / (Real.log x) ^ 4 := by linarith
    · have hUn : (Un : ℝ) < (A : ℝ) * S := by
        have h1 : Un < A * scale := not_le.mp hAle
        have h2 : (Un : ℝ) < ((A * scale : ℕ) : ℝ) := by exact_mod_cast h1
        simpa using h2
      have h1 : (Un : ℝ) < S * x := by nlinarith [hUn, hAx, hSpos]
      linarith

theorem lo_step {x : ℝ} {Cn An Ln dn lhin : ℕ} (hx : 1 < x) (hAnx : (An : ℝ) ≤ x)
    (hxCn : x ≤ (Cn : ℝ)) (hlhi : S * Real.log x ≤ (lhin : ℝ))
    (hchk : (((Cn * scale - Ln) - dn : ℕ) : ℝ) * (lhin : ℝ) ^ 4 < 100 * (An : ℝ) * S ^ 5) :
    S * x - 100 * S * x / (Real.log x) ^ 4 < (Ln : ℝ) + (dn : ℝ) := by
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hSpos : 0 < S := S_pos
  have htpos : 0 < 100 * S * x / (Real.log x) ^ 4 := by
    apply div_pos
    · positivity
    · exact pow_pos hlogx 4
  by_cases hle : Cn * scale ≤ Ln + dn
  · have h1 : S * x ≤ (Cn : ℝ) * S := by nlinarith [hxCn, hSpos]
    have h2 : (Cn : ℝ) * S ≤ (Ln : ℝ) + (dn : ℝ) := by exact_mod_cast hle
    linarith
  · have hgen : Ln + dn ≤ Cn * scale := le_of_lt (not_le.mp hle)
    have hD : (((Cn * scale - Ln) - dn : ℕ) : ℝ) = (Cn : ℝ) * S - (Ln : ℝ) - (dn : ℝ) := by
      rw [Nat.cast_sub (show dn ≤ Cn * scale - Ln by omega),
        Nat.cast_sub (show Ln ≤ Cn * scale by omega)]
      push_cast
      ring
    rw [hD] at hchk
    have hlhin_pos : (0 : ℝ) < (lhin : ℝ) ^ 4 := by
      have : (0 : ℝ) < (lhin : ℝ) := lt_of_lt_of_le (mul_pos hSpos hlogx) hlhi
      exact pow_pos this 4
    have hpow : (S * Real.log x) ^ 4 ≤ (lhin : ℝ) ^ 4 :=
      pow_le_pow_left₀ (mul_nonneg hSpos.le hlogx.le) hlhi 4
    have h1 : 100 * (An : ℝ) * S ^ 5 / (lhin : ℝ) ^ 4 ≤
        100 * (An : ℝ) * S ^ 5 / (S * Real.log x) ^ 4 :=
      div_le_div_of_nonneg_left (by positivity)
        (pow_pos (mul_pos hSpos hlogx) 4) hpow
    have h2 : 100 * (An : ℝ) * S ^ 5 / (S * Real.log x) ^ 4 =
        100 * (An : ℝ) * S / (Real.log x) ^ 4 := by
      rw [mul_pow]
      field_simp
    have h3 : 100 * (An : ℝ) * S / (Real.log x) ^ 4 ≤
        100 * S * x / (Real.log x) ^ 4 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [hAnx, hSpos]
    have hdiv : (Cn : ℝ) * S - (Ln : ℝ) - (dn : ℝ) <
        100 * (An : ℝ) * S ^ 5 / (lhin : ℝ) ^ 4 := by
      rw [lt_div_iff₀ hlhin_pos]
      linarith
    have hxle : S * x ≤ (Cn : ℝ) * S := by nlinarith [hxCn, hSpos]
    calc S * x - 100 * S * x / (Real.log x) ^ 4
        ≤ (Cn : ℝ) * S - 100 * S * x / (Real.log x) ^ 4 := by linarith
      _ < (Ln : ℝ) + (dn : ℝ) := by linarith

-- ============================================================
-- Mask slice: number of primes and primality from bits
-- ============================================================

theorem blkCnt_eq {gbase top a b : ℕ} (hbase : gbase ≤ a) (hb1 : 1 ≤ gbase)
    (hsq : top ≤ gbase * gbase) (hb : b ≤ top) (h8 : b ≤ 10 ^ 8) :
    bitCount (depthFor (b - a)) (mask gbase top / 2 ^ (a - gbase) % 2 ^ (b - a)) =
      ((Nat.primesLE b).filter (fun p => a < p)).card := by
  exact (bitCount_sound (depthFor (b - a))
      (mask gbase top / 2 ^ (a - gbase) % 2 ^ (b - a)) (b - a)
      (Nat.mod_lt _ (Nat.two_pow_pos (b - a))) (depthFor_covers (b - a))).trans
    (AxlerSieve.candidateCount_slice_eq hbase hb1 hsq hb h8)

theorem blk_prime_of_bit {gbase top m a b p : ℕ}
    (hm : m = mask gbase top) (hbase : gbase ≤ a) (hb1 : 1 ≤ gbase)
    (hsq : top ≤ gbase * gbase) (h8 : p ≤ 10 ^ 8) (hpa : a < p) (hpb : p ≤ b)
    (hbtop : b ≤ top)
    (hbit : (m / 2 ^ (a - gbase) % 2 ^ (b - a)).testBit (p - a - 1) = true) :
    Nat.Prime p := by
  subst hm
  rw [AxlerSieve.slice_bit (a := a) (b := b) (m := mask gbase top) (by omega)] at hbit
  have hidx : a - gbase + (p - a - 1) = (p - 1) - gbase + 0 := by omega
  rw [hidx] at hbit
  have h := (AxlerSieve.mask_bit_iff (base := gbase) (top := top) (a := p - 1) (i := 0)
    (by omega) hb1 hsq (by omega) (by omega)).mp hbit
  have hp1 : 1 ≤ p := by omega
  simpa [Nat.sub_add_cancel hp1] using h

-- ============================================================
-- Block specification
-- ============================================================


theorem blkOK_spec {gbase m : ℕ} {B : Blk} {L U L' U' : ℕ}
    (h : blkOK gbase m B L U = (true, L', U')) :
    (fun (gbase m : ℕ) (B : Blk) (L U L' U' : ℕ) => ∃ w cnt llo lhi : ℕ,
    w = m / 2 ^ (B.1 - gbase) % 2 ^ (B.2.1 - B.1) ∧
    cnt = bitCount (depthFor (B.2.1 - B.1)) w ∧
    llo = logLoNum (B.1 + 1) ∧
    lhi = logUpNum B.2.1 ∧
    L' = L + cnt * llo ∧
    U' = U + cnt * lhi ∧
    (B.1 < gate ∨
      (cnt = 0 ∧
        (B.2.1 * scale - L) * lhi ^ 4 < 100 * B.1 * scale ^ 5 ∧
        (U < B.1 * scale ∨ (U - B.1 * scale) * lhi ^ 4 < 100 * B.1 * scale ^ 5)) ∨
      (cnt ≠ 0 ∧
        (B.1 < B.2.2.1 ∧ B.2.2.1 ≤ B.2.1 ∧ w % 2 ^ (B.2.2.1 - B.1 - 1) = 0 ∧
          w.testBit (B.2.2.1 - B.1 - 1) = true) ∧
        ((cnt < 2 ∧ B.2.2.2.1 = 0) ∨
          (2 ≤ cnt ∧ B.2.2.1 < B.2.2.2.1 ∧ B.2.2.2.1 ≤ B.2.1 ∧ w.testBit (B.2.2.2.1 - B.1 - 1) = true)) ∧
        ((cnt < 3 ∧ B.2.2.2.2 = 0) ∨
          (3 ≤ cnt ∧ B.2.2.2.1 < B.2.2.2.2 ∧ B.2.2.2.2 ≤ B.2.1 ∧ w.testBit (B.2.2.2.2 - B.1 - 1) = true)) ∧
        ((U + cnt * lhi < B.1 * scale) ∨
          ((U + cnt * lhi - B.1 * scale) * lhi ^ 4 < 100 * B.1 * scale ^ 5)) ∧
        ((B.2.2.1 * scale - L) * lhi ^ 4 < 100 * B.1 * scale ^ 5) ∧
        (((if 2 ≤ cnt then B.2.2.2.1 else B.2.1) * scale - L - llo) * lhi ^ 4 <
          100 * B.2.2.1 * scale ^ 5) ∧
        (cnt < 2 ∨ (((if 3 ≤ cnt then B.2.2.2.2 else B.2.1) * scale - L - 2 * llo) * lhi ^ 4 <
          100 * B.2.2.2.1 * scale ^ 5)) ∧
        (cnt < 3 ∨ ((B.2.1 * scale - L - 3 * llo) * lhi ^ 4 < 100 * B.2.2.2.2 * scale ^ 5)) ∧
        (B.1 = gate → (U - B.1 * scale) * (logUpNum B.1) ^ 4 < 100 * B.1 * scale ^ 5 ∧
          (B.1 * scale - L) * (logUpNum B.1) ^ 4 < 100 * B.1 * scale ^ 5)))) gbase m B L U L' U' := by
  unfold blkOK at *
  dsimp only at *
  simp only [RosserPackedBarrier.forceNat_eq] at h ⊢
  by_cases hg : B.1 < gate
  · by_cases hcnt : bitCount (depthFor (B.2.1 - B.1)) (m / 2 ^ (B.1 - gbase) % 2 ^ (B.2.1 - B.1)) = 0
    · simp only [if_pos hcnt, if_pos hg] at h
      have hfst : L = L' := congrArg Prod.fst (congrArg Prod.snd h)
      have hsnd : U = U' := congrArg Prod.snd (congrArg Prod.snd h)
      exact ⟨_, _, _, _, rfl, rfl, rfl, rfl,
        by rw [← hfst]; simp [hcnt], by rw [← hsnd]; simp [hcnt], Or.inl hg⟩
    · simp only [if_neg hcnt, if_pos hg] at h
      have hfst : L + bitCount (depthFor (B.2.1 - B.1))
          (m / 2 ^ (B.1 - gbase) % 2 ^ (B.2.1 - B.1)) * logLoNum (B.1 + 1) = L' :=
        congrArg Prod.fst (congrArg Prod.snd h)
      have hsnd : U + bitCount (depthFor (B.2.1 - B.1))
          (m / 2 ^ (B.1 - gbase) % 2 ^ (B.2.1 - B.1)) * logUpNum B.2.1 = U' :=
        congrArg Prod.snd (congrArg Prod.snd h)
      exact ⟨_, _, _, _, rfl, rfl, rfl, rfl, hfst.symm, hsnd.symm, Or.inl hg⟩
  · by_cases hcnt : bitCount (depthFor (B.2.1 - B.1)) (m / 2 ^ (B.1 - gbase) % 2 ^ (B.2.1 - B.1)) = 0
    · simp only [if_pos hcnt, if_neg hg] at h
      have hfst := congrArg Prod.fst h
      have hL' : L = L' := congrArg Prod.fst (congrArg Prod.snd h)
      have hU' : U = U' := congrArg Prod.snd (congrArg Prod.snd h)
      have hdec := of_decide_eq_true hfst
      refine ⟨_, _, _, _, rfl, rfl, rfl, rfl, ?_, ?_,
        Or.inr (Or.inl ⟨hcnt, hdec.1, hdec.2.1⟩)⟩
      · rw [← hL']; simp [hcnt]
      · rw [← hU']; simp [hcnt]
    · simp only [if_neg hcnt, if_neg hg] at h
      have hfst := congrArg Prod.fst h
      have hfst2 : L + bitCount (depthFor (B.2.1 - B.1))
          (m / 2 ^ (B.1 - gbase) % 2 ^ (B.2.1 - B.1)) * logLoNum (B.1 + 1) = L' :=
        congrArg Prod.fst (congrArg Prod.snd h)
      have hsnd2 : U + bitCount (depthFor (B.2.1 - B.1))
          (m / 2 ^ (B.1 - gbase) % 2 ^ (B.2.1 - B.1)) * logUpNum B.2.1 = U' :=
        congrArg Prod.snd (congrArg Prod.snd h)
      have hP := of_decide_eq_true hfst
      exact ⟨_, _, _, _, rfl, rfl, rfl, rfl, hfst2.symm, hsnd2.symm,
        Or.inr (Or.inr ⟨hcnt, hP⟩)⟩


theorem blkOK_spec' {gbase m : ℕ} {B : Blk} {L U L' U' : ℕ} {ok : Bool}
    (h : blkOK gbase m B L U = (ok, L', U')) (hok : ok = true) :
    (fun (gbase m : ℕ) (B : Blk) (L U L' U' : ℕ) => ∃ w cnt llo lhi : ℕ,
    w = m / 2 ^ (B.1 - gbase) % 2 ^ (B.2.1 - B.1) ∧
    cnt = bitCount (depthFor (B.2.1 - B.1)) w ∧
    llo = logLoNum (B.1 + 1) ∧
    lhi = logUpNum B.2.1 ∧
    L' = L + cnt * llo ∧
    U' = U + cnt * lhi ∧
    (B.1 < gate ∨
      (cnt = 0 ∧
        (B.2.1 * scale - L) * lhi ^ 4 < 100 * B.1 * scale ^ 5 ∧
        (U < B.1 * scale ∨ (U - B.1 * scale) * lhi ^ 4 < 100 * B.1 * scale ^ 5)) ∨
      (cnt ≠ 0 ∧
        (B.1 < B.2.2.1 ∧ B.2.2.1 ≤ B.2.1 ∧ w % 2 ^ (B.2.2.1 - B.1 - 1) = 0 ∧
          w.testBit (B.2.2.1 - B.1 - 1) = true) ∧
        ((cnt < 2 ∧ B.2.2.2.1 = 0) ∨
          (2 ≤ cnt ∧ B.2.2.1 < B.2.2.2.1 ∧ B.2.2.2.1 ≤ B.2.1 ∧ w.testBit (B.2.2.2.1 - B.1 - 1) = true)) ∧
        ((cnt < 3 ∧ B.2.2.2.2 = 0) ∨
          (3 ≤ cnt ∧ B.2.2.2.1 < B.2.2.2.2 ∧ B.2.2.2.2 ≤ B.2.1 ∧ w.testBit (B.2.2.2.2 - B.1 - 1) = true)) ∧
        ((U + cnt * lhi < B.1 * scale) ∨
          ((U + cnt * lhi - B.1 * scale) * lhi ^ 4 < 100 * B.1 * scale ^ 5)) ∧
        ((B.2.2.1 * scale - L) * lhi ^ 4 < 100 * B.1 * scale ^ 5) ∧
        (((if 2 ≤ cnt then B.2.2.2.1 else B.2.1) * scale - L - llo) * lhi ^ 4 <
          100 * B.2.2.1 * scale ^ 5) ∧
        (cnt < 2 ∨ (((if 3 ≤ cnt then B.2.2.2.2 else B.2.1) * scale - L - 2 * llo) * lhi ^ 4 <
          100 * B.2.2.2.1 * scale ^ 5)) ∧
        (cnt < 3 ∨ ((B.2.1 * scale - L - 3 * llo) * lhi ^ 4 < 100 * B.2.2.2.2 * scale ^ 5)) ∧
        (B.1 = gate → (U - B.1 * scale) * (logUpNum B.1) ^ 4 < 100 * B.1 * scale ^ 5 ∧
          (B.1 * scale - L) * (logUpNum B.1) ^ 4 < 100 * B.1 * scale ^ 5)))) gbase m B L U L' U' :=
  blkOK_spec (by rw [hok] at h; exact h)

theorem grpGo_spec (G : Grp) (gbase m : ℕ) :
    ∀ (prev L U : ℕ) (blks : List Blk),
      grpGo G gbase m prev L U blks = true → (fun (G : Grp) (gbase m prev L U : ℕ) (blks : List Blk) =>
  (blks.foldr (fun B acc => fun prev L U =>
    prev = B.1 ∧ ∃ L' U', (fun (gbase m : ℕ) (B : Blk) (L U L' U' : ℕ) => ∃ w cnt llo lhi : ℕ,
    w = m / 2 ^ (B.1 - gbase) % 2 ^ (B.2.1 - B.1) ∧
    cnt = bitCount (depthFor (B.2.1 - B.1)) w ∧
    llo = logLoNum (B.1 + 1) ∧
    lhi = logUpNum B.2.1 ∧
    L' = L + cnt * llo ∧
    U' = U + cnt * lhi ∧
    (B.1 < gate ∨
      (cnt = 0 ∧
        (B.2.1 * scale - L) * lhi ^ 4 < 100 * B.1 * scale ^ 5 ∧
        (U < B.1 * scale ∨ (U - B.1 * scale) * lhi ^ 4 < 100 * B.1 * scale ^ 5)) ∨
      (cnt ≠ 0 ∧
        (B.1 < B.2.2.1 ∧ B.2.2.1 ≤ B.2.1 ∧ w % 2 ^ (B.2.2.1 - B.1 - 1) = 0 ∧
          w.testBit (B.2.2.1 - B.1 - 1) = true) ∧
        ((cnt < 2 ∧ B.2.2.2.1 = 0) ∨
          (2 ≤ cnt ∧ B.2.2.1 < B.2.2.2.1 ∧ B.2.2.2.1 ≤ B.2.1 ∧ w.testBit (B.2.2.2.1 - B.1 - 1) = true)) ∧
        ((cnt < 3 ∧ B.2.2.2.2 = 0) ∨
          (3 ≤ cnt ∧ B.2.2.2.1 < B.2.2.2.2 ∧ B.2.2.2.2 ≤ B.2.1 ∧ w.testBit (B.2.2.2.2 - B.1 - 1) = true)) ∧
        ((U + cnt * lhi < B.1 * scale) ∨
          ((U + cnt * lhi - B.1 * scale) * lhi ^ 4 < 100 * B.1 * scale ^ 5)) ∧
        ((B.2.2.1 * scale - L) * lhi ^ 4 < 100 * B.1 * scale ^ 5) ∧
        (((if 2 ≤ cnt then B.2.2.2.1 else B.2.1) * scale - L - llo) * lhi ^ 4 <
          100 * B.2.2.1 * scale ^ 5) ∧
        (cnt < 2 ∨ (((if 3 ≤ cnt then B.2.2.2.2 else B.2.1) * scale - L - 2 * llo) * lhi ^ 4 <
          100 * B.2.2.2.1 * scale ^ 5)) ∧
        (cnt < 3 ∨ ((B.2.1 * scale - L - 3 * llo) * lhi ^ 4 < 100 * B.2.2.2.2 * scale ^ 5)) ∧
        (B.1 = gate → (U - B.1 * scale) * (logUpNum B.1) ^ 4 < 100 * B.1 * scale ^ 5 ∧
          (B.1 * scale - L) * (logUpNum B.1) ^ 4 < 100 * B.1 * scale ^ 5)))) gbase m B L U L' U' ∧ acc B.2.1 L' U')
    (fun prev L U => prev = G.2.1 ∧ L = G.2.2.2.2.1 ∧ U = G.2.2.2.2.2.1)) prev L U) G gbase m prev L U blks := by
  intro prev L U blks
  induction blks generalizing prev L U with
  | nil =>
    intro h
    simp only [grpGo, List.foldr] at h ⊢
    simpa [and_assoc] using h
  | cons B rest ih =>
    intro h
    simp only [grpGo] at h
    cases hb : blkOK gbase m B L U with
    | mk ok st =>
      rw [hb] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hprev, hok⟩, hrest⟩ := h
      exact ⟨hprev, st.1, st.2, blkOK_spec' hb hok, ih B.2.1 st.1 st.2 hrest⟩

theorem grpOK_spec {G : Grp} (h : grpOK G = true) :
    (fun (G : Grp) (gbase m prev L U : ℕ) (blks : List Blk) =>
  (blks.foldr (fun B acc => fun prev L U =>
    prev = B.1 ∧ ∃ L' U', (fun (gbase m : ℕ) (B : Blk) (L U L' U' : ℕ) => ∃ w cnt llo lhi : ℕ,
    w = m / 2 ^ (B.1 - gbase) % 2 ^ (B.2.1 - B.1) ∧
    cnt = bitCount (depthFor (B.2.1 - B.1)) w ∧
    llo = logLoNum (B.1 + 1) ∧
    lhi = logUpNum B.2.1 ∧
    L' = L + cnt * llo ∧
    U' = U + cnt * lhi ∧
    (B.1 < gate ∨
      (cnt = 0 ∧
        (B.2.1 * scale - L) * lhi ^ 4 < 100 * B.1 * scale ^ 5 ∧
        (U < B.1 * scale ∨ (U - B.1 * scale) * lhi ^ 4 < 100 * B.1 * scale ^ 5)) ∨
      (cnt ≠ 0 ∧
        (B.1 < B.2.2.1 ∧ B.2.2.1 ≤ B.2.1 ∧ w % 2 ^ (B.2.2.1 - B.1 - 1) = 0 ∧
          w.testBit (B.2.2.1 - B.1 - 1) = true) ∧
        ((cnt < 2 ∧ B.2.2.2.1 = 0) ∨
          (2 ≤ cnt ∧ B.2.2.1 < B.2.2.2.1 ∧ B.2.2.2.1 ≤ B.2.1 ∧ w.testBit (B.2.2.2.1 - B.1 - 1) = true)) ∧
        ((cnt < 3 ∧ B.2.2.2.2 = 0) ∨
          (3 ≤ cnt ∧ B.2.2.2.1 < B.2.2.2.2 ∧ B.2.2.2.2 ≤ B.2.1 ∧ w.testBit (B.2.2.2.2 - B.1 - 1) = true)) ∧
        ((U + cnt * lhi < B.1 * scale) ∨
          ((U + cnt * lhi - B.1 * scale) * lhi ^ 4 < 100 * B.1 * scale ^ 5)) ∧
        ((B.2.2.1 * scale - L) * lhi ^ 4 < 100 * B.1 * scale ^ 5) ∧
        (((if 2 ≤ cnt then B.2.2.2.1 else B.2.1) * scale - L - llo) * lhi ^ 4 <
          100 * B.2.2.1 * scale ^ 5) ∧
        (cnt < 2 ∨ (((if 3 ≤ cnt then B.2.2.2.2 else B.2.1) * scale - L - 2 * llo) * lhi ^ 4 <
          100 * B.2.2.2.1 * scale ^ 5)) ∧
        (cnt < 3 ∨ ((B.2.1 * scale - L - 3 * llo) * lhi ^ 4 < 100 * B.2.2.2.2 * scale ^ 5)) ∧
        (B.1 = gate → (U - B.1 * scale) * (logUpNum B.1) ^ 4 < 100 * B.1 * scale ^ 5 ∧
          (B.1 * scale - L) * (logUpNum B.1) ^ 4 < 100 * B.1 * scale ^ 5)))) gbase m B L U L' U' ∧ acc B.2.1 L' U')
    (fun prev L U => prev = G.2.1 ∧ L = G.2.2.2.2.1 ∧ U = G.2.2.2.2.2.1)) prev L U) G G.1 (mask G.1 G.2.1) G.1 G.2.2.1 G.2.2.2.1 G.2.2.2.2.2.2 := by
  unfold grpOK at h
  simp only [RosserPackedBarrier.forceNat_eq] at h
  exact grpGo_spec G G.1 (mask G.1 G.2.1) G.1 G.2.2.1 G.2.2.2.1 G.2.2.2.2.2.2 h

-- ============================================================
-- State advance and range soundness
-- ============================================================

theorem blk_state {gbase top m : ℕ} {B : Blk} {L U L' U' : ℕ}
    (hm : m = mask gbase top) (h : (fun (gbase m : ℕ) (B : Blk) (L U L' U' : ℕ) => ∃ w cnt llo lhi : ℕ,
    w = m / 2 ^ (B.1 - gbase) % 2 ^ (B.2.1 - B.1) ∧
    cnt = bitCount (depthFor (B.2.1 - B.1)) w ∧
    llo = logLoNum (B.1 + 1) ∧
    lhi = logUpNum B.2.1 ∧
    L' = L + cnt * llo ∧
    U' = U + cnt * lhi ∧
    (B.1 < gate ∨
      (cnt = 0 ∧
        (B.2.1 * scale - L) * lhi ^ 4 < 100 * B.1 * scale ^ 5 ∧
        (U < B.1 * scale ∨ (U - B.1 * scale) * lhi ^ 4 < 100 * B.1 * scale ^ 5)) ∨
      (cnt ≠ 0 ∧
        (B.1 < B.2.2.1 ∧ B.2.2.1 ≤ B.2.1 ∧ w % 2 ^ (B.2.2.1 - B.1 - 1) = 0 ∧
          w.testBit (B.2.2.1 - B.1 - 1) = true) ∧
        ((cnt < 2 ∧ B.2.2.2.1 = 0) ∨
          (2 ≤ cnt ∧ B.2.2.1 < B.2.2.2.1 ∧ B.2.2.2.1 ≤ B.2.1 ∧ w.testBit (B.2.2.2.1 - B.1 - 1) = true)) ∧
        ((cnt < 3 ∧ B.2.2.2.2 = 0) ∨
          (3 ≤ cnt ∧ B.2.2.2.1 < B.2.2.2.2 ∧ B.2.2.2.2 ≤ B.2.1 ∧ w.testBit (B.2.2.2.2 - B.1 - 1) = true)) ∧
        ((U + cnt * lhi < B.1 * scale) ∨
          ((U + cnt * lhi - B.1 * scale) * lhi ^ 4 < 100 * B.1 * scale ^ 5)) ∧
        ((B.2.2.1 * scale - L) * lhi ^ 4 < 100 * B.1 * scale ^ 5) ∧
        (((if 2 ≤ cnt then B.2.2.2.1 else B.2.1) * scale - L - llo) * lhi ^ 4 <
          100 * B.2.2.1 * scale ^ 5) ∧
        (cnt < 2 ∨ (((if 3 ≤ cnt then B.2.2.2.2 else B.2.1) * scale - L - 2 * llo) * lhi ^ 4 <
          100 * B.2.2.2.1 * scale ^ 5)) ∧
        (cnt < 3 ∨ ((B.2.1 * scale - L - 3 * llo) * lhi ^ 4 < 100 * B.2.2.2.2 * scale ^ 5)) ∧
        (B.1 = gate → (U - B.1 * scale) * (logUpNum B.1) ^ 4 < 100 * B.1 * scale ^ 5 ∧
          (B.1 * scale - L) * (logUpNum B.1) ^ 4 < 100 * B.1 * scale ^ 5)))) gbase m B L U L' U')
    (hbase : gbase ≤ B.1) (hb1 : 1 ≤ gbase) (hsq : top ≤ gbase * gbase)
    (hbtop : B.2.1 ≤ top) (h8top : top ≤ 10 ^ 8)
    (ha1 : 1 ≤ B.1) (hab : B.1 < B.2.1)
    (hL : (L : ℝ) ≤ S * Chebyshev.theta (B.1 : ℝ))
    (hU : S * Chebyshev.theta (B.1 : ℝ) ≤ (U : ℝ)) :
    (L' : ℝ) ≤ S * Chebyshev.theta (B.2.1 : ℝ) ∧
      S * Chebyshev.theta (B.2.1 : ℝ) ≤ (U' : ℝ) := by
  try dsimp only at h
  obtain ⟨w, cnt, llo, lhi, hw, hcnt, hllo, hlhi, hL'e, hU'e, hcase⟩ := h
  have h10_64 : (10 : ℕ) ^ 8 < 2 ^ 64 := by norm_num
  have h8 : B.2.1 ≤ 10 ^ 8 := by omega
  have hb64 : B.2.1 < 2 ^ 64 := by omega
  have hcard : cnt = ((Nat.primesLE B.2.1).filter (fun p => B.1 < p)).card := by
    rw [hcnt, hw, hm]
    exact blkCnt_eq hbase hb1 hsq hbtop h8
  have hL'eR : (L' : ℝ) = (L : ℝ) + (cnt : ℝ) * (llo : ℝ) := by
    rw [hL'e, Nat.cast_add, Nat.cast_mul]
  have hU'eR : (U' : ℝ) = (U : ℝ) + (cnt : ℝ) * (lhi : ℝ) := by
    rw [hU'e, Nat.cast_add, Nat.cast_mul]
  by_cases hc0 : cnt = 0
  · have hcard0 : ((Nat.primesLE B.2.1).filter (fun p => B.1 < p)).card = 0 := by
      rw [← hcard, hc0]
    have hempty := Finset.card_eq_zero.mp hcard0
    have hno : ∀ p, Nat.Prime p → B.1 < p → p ≤ B.2.1 → False := by
      intro p hp hap hpb
      have hmem : p ∈ (Nat.primesLE B.2.1).filter (fun p => B.1 < p) :=
        Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpb, hp⟩, hap⟩
      rw [hempty] at hmem
      exact Finset.notMem_empty p hmem
    have hθ : Chebyshev.theta (B.2.1 : ℝ) = Chebyshev.theta (B.1 : ℝ) :=
      theta_eq_of_no_primes B.1 B.2.1 (le_of_lt hab) hno
    have hcntR : (cnt : ℝ) = 0 := by exact_mod_cast hc0
    constructor
    · calc (L' : ℝ) = (L : ℝ) + (cnt : ℝ) * (llo : ℝ) := hL'eR
        _ = (L : ℝ) := by rw [hcntR]; ring
        _ ≤ S * Chebyshev.theta (B.2.1 : ℝ) := by rw [hθ]; exact hL
    · calc S * Chebyshev.theta (B.2.1 : ℝ) = S * Chebyshev.theta (B.1 : ℝ) := by rw [hθ]
        _ ≤ (U : ℝ) := hU
        _ = (U' : ℝ) := by rw [hU'eR, hcntR]; ring
  · have hcR : (cnt : ℝ) = (((Nat.primesLE B.2.1).filter (fun p => B.1 < p)).card : ℝ) := by
      exact_mod_cast hcard
    have hlo := theta_lo_card (a := B.1) (b := B.2.1) ha1 hab hb64
    have hup := theta_up_card (a := B.1) (b := B.2.1) ha1 hab hb64
    constructor
    · calc (L' : ℝ) = (L : ℝ) + (cnt : ℝ) * (llo : ℝ) := hL'eR
        _ ≤ S * Chebyshev.theta (B.1 : ℝ) +
            S * (Chebyshev.theta (B.2.1 : ℝ) - Chebyshev.theta (B.1 : ℝ)) := by
            rw [hcR, hllo]; linarith [hL, hlo]
        _ = S * Chebyshev.theta (B.2.1 : ℝ) := by ring
    · calc S * Chebyshev.theta (B.2.1 : ℝ)
          = S * Chebyshev.theta (B.1 : ℝ) +
            S * (Chebyshev.theta (B.2.1 : ℝ) - Chebyshev.theta (B.1 : ℝ)) := by ring
        _ ≤ (U : ℝ) + (cnt : ℝ) * (lhi : ℝ) := by rw [hcR, hlhi]; linarith [hU, hup]
        _ = (U' : ℝ) := hU'eR.symm

theorem blk_range {gbase top m : ℕ} {B : Blk} {L U L' U' : ℕ}
    (hm : m = mask gbase top) (h : (fun (gbase m : ℕ) (B : Blk) (L U L' U' : ℕ) => ∃ w cnt llo lhi : ℕ,
    w = m / 2 ^ (B.1 - gbase) % 2 ^ (B.2.1 - B.1) ∧
    cnt = bitCount (depthFor (B.2.1 - B.1)) w ∧
    llo = logLoNum (B.1 + 1) ∧
    lhi = logUpNum B.2.1 ∧
    L' = L + cnt * llo ∧
    U' = U + cnt * lhi ∧
    (B.1 < gate ∨
      (cnt = 0 ∧
        (B.2.1 * scale - L) * lhi ^ 4 < 100 * B.1 * scale ^ 5 ∧
        (U < B.1 * scale ∨ (U - B.1 * scale) * lhi ^ 4 < 100 * B.1 * scale ^ 5)) ∨
      (cnt ≠ 0 ∧
        (B.1 < B.2.2.1 ∧ B.2.2.1 ≤ B.2.1 ∧ w % 2 ^ (B.2.2.1 - B.1 - 1) = 0 ∧
          w.testBit (B.2.2.1 - B.1 - 1) = true) ∧
        ((cnt < 2 ∧ B.2.2.2.1 = 0) ∨
          (2 ≤ cnt ∧ B.2.2.1 < B.2.2.2.1 ∧ B.2.2.2.1 ≤ B.2.1 ∧ w.testBit (B.2.2.2.1 - B.1 - 1) = true)) ∧
        ((cnt < 3 ∧ B.2.2.2.2 = 0) ∨
          (3 ≤ cnt ∧ B.2.2.2.1 < B.2.2.2.2 ∧ B.2.2.2.2 ≤ B.2.1 ∧ w.testBit (B.2.2.2.2 - B.1 - 1) = true)) ∧
        ((U + cnt * lhi < B.1 * scale) ∨
          ((U + cnt * lhi - B.1 * scale) * lhi ^ 4 < 100 * B.1 * scale ^ 5)) ∧
        ((B.2.2.1 * scale - L) * lhi ^ 4 < 100 * B.1 * scale ^ 5) ∧
        (((if 2 ≤ cnt then B.2.2.2.1 else B.2.1) * scale - L - llo) * lhi ^ 4 <
          100 * B.2.2.1 * scale ^ 5) ∧
        (cnt < 2 ∨ (((if 3 ≤ cnt then B.2.2.2.2 else B.2.1) * scale - L - 2 * llo) * lhi ^ 4 <
          100 * B.2.2.2.1 * scale ^ 5)) ∧
        (cnt < 3 ∨ ((B.2.1 * scale - L - 3 * llo) * lhi ^ 4 < 100 * B.2.2.2.2 * scale ^ 5)) ∧
        (B.1 = gate → (U - B.1 * scale) * (logUpNum B.1) ^ 4 < 100 * B.1 * scale ^ 5 ∧
          (B.1 * scale - L) * (logUpNum B.1) ^ 4 < 100 * B.1 * scale ^ 5)))) gbase m B L U L' U')
    (hbase : gbase ≤ B.1) (hb1 : 1 ≤ gbase) (hsq : top ≤ gbase * gbase)
    (hbtop : B.2.1 ≤ top) (h8top : top ≤ 10 ^ 8)
    (hgate : gate ≤ B.1) (hab : B.1 < B.2.1)
    (hL : (L : ℝ) ≤ S * Chebyshev.theta (B.1 : ℝ))
    (hUb : S * Chebyshev.theta (B.2.1 : ℝ) ≤ (U' : ℝ)) :
    ∀ x : ℝ, (B.1 : ℝ) ≤ x → x ≤ (B.2.1 : ℝ) →
      |Chebyshev.theta x - x| < 100 * x / (Real.log x) ^ 4 := by
  try dsimp only at h
  obtain ⟨w, cnt, llo, lhi, hw, hcnt, hllo, hlhi, hL'e, hU'e, hcase⟩ := h
  have hgate' : 70111 ≤ B.1 := by simpa only [gate] using hgate
  have ha1 : 1 ≤ B.1 := by omega
  have h10_64 : (10 : ℕ) ^ 8 < 2 ^ 64 := by norm_num
  have h8 : B.2.1 ≤ 10 ^ 8 := by omega
  have hb64 : B.2.1 < 2 ^ 64 := by omega
  intro x hax hxb
  have hx1 : 1 < x := by
    have h1 : (1 : ℝ) < (B.1 : ℝ) := by
      have h2 : (1 : ℕ) < B.1 := by omega
      exact_mod_cast h2
    linarith
  have hlhix : S * Real.log x ≤ (lhi : ℝ) := by
    have h1 : Real.log x ≤ Real.log (B.2.1 : ℝ) := Real.log_le_log (by linarith) hxb
    have h2 := logUpNum_sound B.2.1 (by omega) hb64
    have h3 : S * Real.log x ≤ S * Real.log (B.2.1 : ℝ) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    rw [hlhi]
    linarith
  rcases hcase with hg | ⟨hc0, hLOc, hHI0⟩ | ⟨hcne, hP⟩
  · exact absurd hg (not_lt.mpr hgate)
  · have hU'eq : U' = U := by rw [hU'e, hc0]; ring
    have hchk : (U' : ℝ) < (B.1 : ℝ) * S ∨
        (((U' - B.1 * scale : ℕ) : ℝ) * (lhi : ℝ) ^ 4 < 100 * (B.1 : ℝ) * S ^ 5) := by
      rw [hU'eq]
      rcases hHI0 with h | h
      · left; exact_mod_cast h
      · right; exact cast_check h
    have hupper : S * Chebyshev.theta x < S * x + 100 * S * x / (Real.log x) ^ 4 :=
      lt_of_le_of_lt
        (le_trans (mul_le_mul_of_nonneg_left (Chebyshev.theta_mono hxb) (by positivity)) hUb)
        (hi_step hx1 hax hlhix hchk)
    have hchk2 : (((B.2.1 * scale - L) - 0 : ℕ) : ℝ) * (lhi : ℝ) ^ 4 <
        100 * (B.1 : ℝ) * S ^ 5 := cast_check (by simpa using hLOc)
    have hstep := lo_step (Cn := B.2.1) (An := B.1) (Ln := L) (dn := 0) hx1 hax hxb hlhix hchk2
    have hlow : (L : ℝ) ≤ S * Chebyshev.theta x :=
      le_trans hL (mul_le_mul_of_nonneg_left (Chebyshev.theta_mono hax) (by positivity))
    have hlo : S * x - 100 * S * x / (Real.log x) ^ 4 < S * Chebyshev.theta x := by
      linarith [hstep, hlow]
    exact abs_bound_of S_pos hlo hupper
  · rcases hP with ⟨hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9⟩
    have hp1a : B.1 < B.2.2.1 := hA1.1
    have hp1b : B.2.2.1 ≤ B.2.1 := hA1.2.1
    have hbit1 : w.testBit (B.2.2.1 - B.1 - 1) = true := hA1.2.2.2
    have hp1p : Nat.Prime B.2.2.1 :=
      blk_prime_of_bit hm hbase hb1 hsq (by omega) hp1a hp1b hbtop (by rw [← hw]; exact hbit1)
    have hchkU : (U' : ℝ) < (B.1 : ℝ) * S ∨
        (((U' - B.1 * scale : ℕ) : ℝ) * (lhi : ℝ) ^ 4 < 100 * (B.1 : ℝ) * S ^ 5) := by
      rw [hU'e]
      rcases hA4 with h | h
      · left; exact_mod_cast h
      · right; exact cast_check h
    have hupper : S * Chebyshev.theta x < S * x + 100 * S * x / (Real.log x) ^ 4 :=
      lt_of_le_of_lt
        (le_trans (mul_le_mul_of_nonneg_left (Chebyshev.theta_mono hxb) (by positivity)) hUb)
        (hi_step hx1 hax hlhix hchkU)
    have hbuf1 : (B.2.2.1 : ℝ) ≤ x → (L : ℝ) + (llo : ℝ) ≤ S * Chebyshev.theta x := by
      intro hp1x
      have hcard1 : 1 ≤ ((Nat.primesLE B.2.2.1).filter (fun p => B.1 < p)).card :=
        Finset.card_pos.mpr ⟨B.2.2.1, Finset.mem_filter.mpr
          ⟨Nat.mem_primesLE.mpr ⟨le_rfl, hp1p⟩, hp1a⟩⟩
      have hlo1 := theta_lo_card (a := B.1) (b := B.2.2.1) ha1 hp1a (by omega)
      rw [← hllo] at hlo1
      have hc1 : (1 : ℝ) ≤ (((Nat.primesLE B.2.2.1).filter (fun p => B.1 < p)).card : ℝ) := by
        exact_mod_cast hcard1
      have hllo0 : (0 : ℝ) ≤ (llo : ℝ) := by positivity
      have h1 : (llo : ℝ) ≤
          (((Nat.primesLE B.2.2.1).filter (fun p => B.1 < p)).card : ℝ) * (llo : ℝ) := by
        have h2 := mul_le_mul_of_nonneg_right hc1 hllo0
        simpa using h2
      calc (L : ℝ) + (llo : ℝ)
          ≤ S * Chebyshev.theta (B.1 : ℝ) +
            S * (Chebyshev.theta (B.2.2.1 : ℝ) - Chebyshev.theta (B.1 : ℝ)) := by
            linarith [hL, hlo1, h1]
        _ = S * Chebyshev.theta (B.2.2.1 : ℝ) := by ring
        _ ≤ S * Chebyshev.theta x :=
            mul_le_mul_of_nonneg_left (Chebyshev.theta_mono hp1x) (by positivity)
    by_cases hx1p : x < (B.2.2.1 : ℝ)
    · have hchk : (((B.2.2.1 * scale - L) - 0 : ℕ) : ℝ) * (lhi : ℝ) ^ 4 <
          100 * (B.1 : ℝ) * S ^ 5 := cast_check (by simpa using hA5)
      have hstep := lo_step (Cn := B.2.2.1) (An := B.1) (Ln := L) (dn := 0) hx1 hax
        (le_of_lt hx1p) hlhix hchk
      have hlow : (L : ℝ) ≤ S * Chebyshev.theta x :=
        le_trans hL (mul_le_mul_of_nonneg_left (Chebyshev.theta_mono hax) (by positivity))
      have hlo : S * x - 100 * S * x / (Real.log x) ^ 4 < S * Chebyshev.theta x := by
        linarith [hstep, hlow]
      exact abs_bound_of S_pos hlo hupper
    · have hp1x : (B.2.2.1 : ℝ) ≤ x := not_lt.mp hx1p
      have hb1x := hbuf1 hp1x
      by_cases h2c : 2 ≤ cnt
      · have hA2' := hA2.resolve_left (by rintro ⟨h1, -⟩; omega)
        have hp12 : B.2.2.1 < B.2.2.2.1 := hA2'.2.1
        have hp2b : B.2.2.2.1 ≤ B.2.1 := hA2'.2.2.1
        have hbit2 : w.testBit (B.2.2.2.1 - B.1 - 1) = true := hA2'.2.2.2
        by_cases hx2p : x < (B.2.2.2.1 : ℝ)
        · have hchk := cast_check (by simpa [if_pos h2c] using hA6)
          have hstep := lo_step (Cn := B.2.2.2.1) (An := B.2.2.1) (Ln := L) (dn := llo) hx1 hp1x
            (le_of_lt hx2p) hlhix hchk
          exact abs_bound_of S_pos (lt_of_lt_of_le hstep hb1x) hupper
        · have hp2x : (B.2.2.2.1 : ℝ) ≤ x := not_lt.mp hx2p
          have hp2p : Nat.Prime B.2.2.2.1 :=
            blk_prime_of_bit hm hbase hb1 hsq (by omega) (lt_trans hp1a hp12) hp2b hbtop
              (by rw [← hw]; exact hbit2)
          have hbuf2 : (L : ℝ) + ((2 * llo : ℕ) : ℝ) ≤ S * Chebyshev.theta x := by
            have hcard2 : 2 ≤ ((Nat.primesLE B.2.2.2.1).filter (fun p => B.1 < p)).card := by
              have hsub : ({B.2.2.1, B.2.2.2.1} : Finset ℕ) ⊆
                  (Nat.primesLE B.2.2.2.1).filter (fun p => B.1 < p) := by
                intro p hp
                rw [Finset.mem_insert, Finset.mem_singleton] at hp
                rcases hp with rfl | rfl
                · exact Finset.mem_filter.mpr
                    ⟨Nat.mem_primesLE.mpr ⟨le_of_lt hp12, hp1p⟩, hp1a⟩
                · exact Finset.mem_filter.mpr
                    ⟨Nat.mem_primesLE.mpr ⟨le_rfl, hp2p⟩, lt_trans hp1a hp12⟩
              have h2 := Finset.card_le_card hsub
              rwa [Finset.card_pair (ne_of_lt hp12)] at h2
            have hlo2 := theta_lo_card (a := B.1) (b := B.2.2.2.1) ha1 (lt_trans hp1a hp12) (by omega)
            rw [← hllo] at hlo2
            have hc2 : (2 : ℝ) ≤
                (((Nat.primesLE B.2.2.2.1).filter (fun p => B.1 < p)).card : ℝ) := by
              exact_mod_cast hcard2
            have hllo0 : (0 : ℝ) ≤ (llo : ℝ) := by positivity
            have h2' : ((2 * llo : ℕ) : ℝ) ≤
                (((Nat.primesLE B.2.2.2.1).filter (fun p => B.1 < p)).card : ℝ) * (llo : ℝ) := by
              calc ((2 * llo : ℕ) : ℝ) = 2 * (llo : ℝ) := by rw [Nat.cast_mul]; norm_num
                _ ≤ (((Nat.primesLE B.2.2.2.1).filter (fun p => B.1 < p)).card : ℝ) * (llo : ℝ) :=
                    mul_le_mul_of_nonneg_right hc2 hllo0
            calc (L : ℝ) + ((2 * llo : ℕ) : ℝ)
                ≤ S * Chebyshev.theta (B.1 : ℝ) +
                  S * (Chebyshev.theta (B.2.2.2.1 : ℝ) - Chebyshev.theta (B.1 : ℝ)) := by
                  linarith [hL, hlo2, h2']
              _ = S * Chebyshev.theta (B.2.2.2.1 : ℝ) := by ring
              _ ≤ S * Chebyshev.theta x :=
                  mul_le_mul_of_nonneg_left (Chebyshev.theta_mono hp2x) (by positivity)
          by_cases h3c : 3 ≤ cnt
          · by_cases hx3p : x < (B.2.2.2.2 : ℝ)
            · have hchk := cast_check (by
                simpa [if_pos h3c] using (hA7.resolve_left (by rintro h1; omega)))
              have hstep := lo_step (Cn := B.2.2.2.2) (An := B.2.2.2.1) (Ln := L) (dn := 2 * llo)
                hx1 hp2x (le_of_lt hx3p) hlhix hchk
              exact abs_bound_of S_pos (lt_of_lt_of_le hstep hbuf2) hupper
            · have hA3' := hA3.resolve_left (by rintro ⟨h1, -⟩; omega)
              have hp23 : B.2.2.2.1 < B.2.2.2.2 := hA3'.2.1
              have hp3b : B.2.2.2.2 ≤ B.2.1 := hA3'.2.2.1
              have hbit3 : w.testBit (B.2.2.2.2 - B.1 - 1) = true := hA3'.2.2.2
              have hp3p : Nat.Prime B.2.2.2.2 :=
                blk_prime_of_bit hm hbase hb1 hsq (by omega)
                  (lt_trans (lt_trans hp1a hp12) hp23) hp3b hbtop
                  (by rw [← hw]; exact hbit3)
              have hp3x : (B.2.2.2.2 : ℝ) ≤ x := not_lt.mp hx3p
              have hbuf3 : (L : ℝ) + ((3 * llo : ℕ) : ℝ) ≤ S * Chebyshev.theta x := by
                have hcard3 : 3 ≤ ((Nat.primesLE B.2.2.2.2).filter (fun p => B.1 < p)).card := by
                  have hsub : ({B.2.2.1, B.2.2.2.1, B.2.2.2.2} : Finset ℕ) ⊆
                      (Nat.primesLE B.2.2.2.2).filter (fun p => B.1 < p) := by
                    intro p hp
                    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
                    rcases hp with rfl | rfl | rfl
                    · exact Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr
                        ⟨le_trans (le_of_lt hp12) (le_of_lt hp23), hp1p⟩, hp1a⟩
                    · exact Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr
                        ⟨le_of_lt hp23, hp2p⟩, lt_trans hp1a hp12⟩
                    · exact Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr
                        ⟨le_rfl, hp3p⟩, lt_trans (lt_trans hp1a hp12) hp23⟩
                  have hcard3eq : ({B.2.2.1, B.2.2.2.1, B.2.2.2.2} : Finset ℕ).card = 3 := by
                    rw [Finset.card_insert_of_notMem (by
                          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                          exact ⟨ne_of_lt hp12, ne_of_lt (lt_trans hp12 hp23)⟩),
                        Finset.card_insert_of_notMem (by simp [ne_of_lt hp23]),
                        Finset.card_singleton]
                  have h3 := Finset.card_le_card hsub
                  rwa [hcard3eq] at h3
                have hlo3 := theta_lo_card (a := B.1) (b := B.2.2.2.2) ha1
                  (lt_trans (lt_trans hp1a hp12) hp23) (by omega)
                rw [← hllo] at hlo3
                have hc3 : (3 : ℝ) ≤
                    (((Nat.primesLE B.2.2.2.2).filter (fun p => B.1 < p)).card : ℝ) := by
                  exact_mod_cast hcard3
                have hllo0 : (0 : ℝ) ≤ (llo : ℝ) := by positivity
                have h3' : ((3 * llo : ℕ) : ℝ) ≤
                    (((Nat.primesLE B.2.2.2.2).filter (fun p => B.1 < p)).card : ℝ) * (llo : ℝ) := by
                  calc ((3 * llo : ℕ) : ℝ) = 3 * (llo : ℝ) := by rw [Nat.cast_mul]; norm_num
                    _ ≤ (((Nat.primesLE B.2.2.2.2).filter (fun p => B.1 < p)).card : ℝ) * (llo : ℝ) :=
                        mul_le_mul_of_nonneg_right hc3 hllo0
                calc (L : ℝ) + ((3 * llo : ℕ) : ℝ)
                    ≤ S * Chebyshev.theta (B.1 : ℝ) +
                      S * (Chebyshev.theta (B.2.2.2.2 : ℝ) - Chebyshev.theta (B.1 : ℝ)) := by
                      linarith [hL, hlo3, h3']
                  _ = S * Chebyshev.theta (B.2.2.2.2 : ℝ) := by ring
                  _ ≤ S * Chebyshev.theta x :=
                      mul_le_mul_of_nonneg_left (Chebyshev.theta_mono hp3x) (by positivity)
              have hchk := cast_check (by simpa using (hA8.resolve_left (by rintro h1; omega)))
              have hstep := lo_step (Cn := B.2.1) (An := B.2.2.2.2) (Ln := L) (dn := 3 * llo)
                hx1 hp3x hxb hlhix hchk
              exact abs_bound_of S_pos (lt_of_lt_of_le hstep hbuf3) hupper
          · have hchk := cast_check (by
              simpa [if_neg h3c] using (hA7.resolve_left (by rintro h1; omega)))
            have hstep := lo_step (Cn := B.2.1) (An := B.2.2.2.1) (Ln := L) (dn := 2 * llo)
              hx1 hp2x hxb hlhix hchk
            exact abs_bound_of S_pos (lt_of_lt_of_le hstep hbuf2) hupper
      · have hchk := cast_check (by simpa [if_neg h2c] using hA6)
        have hstep := lo_step (Cn := B.2.1) (An := B.2.2.1) (Ln := L) (dn := llo)
          hx1 hp1x hxb hlhix hchk
        exact abs_bound_of S_pos (lt_of_lt_of_le hstep hb1x) hupper

-- ============================================================
-- Group-level well-formedness and soundness
-- ============================================================

def grpWF (G : Grp) : Bool :=
  decide (1 ≤ G.1 ∧ 2 ≤ G.1 ∧ G.1 ≤ G.2.1 ∧ G.2.1 ≤ G.1 * G.1 ∧
    G.2.1 ≤ 10 ^ 8) &&
    G.2.2.2.2.2.2.all (fun B => decide (G.1 ≤ B.1 ∧ B.1 < B.2.1 ∧ B.2.1 ≤ G.2.1))

theorem grpWF_spec {G : Grp} (h : grpWF G = true) :
    (1 ≤ G.1 ∧ 2 ≤ G.1 ∧ G.1 ≤ G.2.1 ∧ G.2.1 ≤ G.1 * G.1 ∧
      G.2.1 ≤ 10 ^ 8) ∧
      ∀ B ∈ G.2.2.2.2.2.2, G.1 ≤ B.1 ∧ B.1 < B.2.1 ∧ B.2.1 ≤ G.2.1 := by
  rw [grpWF, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨of_decide_eq_true h1, ?_⟩
  intro B hB
  exact of_decide_eq_true (List.all_eq_true.mp h2 B hB)

theorem grpSpec_state {G : Grp} {gbase m : ℕ} (hm : m = mask gbase G.2.1)
    (hbase1 : 1 ≤ gbase) (hsq : G.2.1 ≤ gbase * gbase) (h8top : G.2.1 ≤ 10 ^ 8) :
    ∀ prev L U blks, (fun (G : Grp) (gbase m prev L U : ℕ) (blks : List Blk) =>
  (blks.foldr (fun B acc => fun prev L U =>
    prev = B.1 ∧ ∃ L' U', (fun (gbase m : ℕ) (B : Blk) (L U L' U' : ℕ) => ∃ w cnt llo lhi : ℕ,
    w = m / 2 ^ (B.1 - gbase) % 2 ^ (B.2.1 - B.1) ∧
    cnt = bitCount (depthFor (B.2.1 - B.1)) w ∧
    llo = logLoNum (B.1 + 1) ∧
    lhi = logUpNum B.2.1 ∧
    L' = L + cnt * llo ∧
    U' = U + cnt * lhi ∧
    (B.1 < gate ∨
      (cnt = 0 ∧
        (B.2.1 * scale - L) * lhi ^ 4 < 100 * B.1 * scale ^ 5 ∧
        (U < B.1 * scale ∨ (U - B.1 * scale) * lhi ^ 4 < 100 * B.1 * scale ^ 5)) ∨
      (cnt ≠ 0 ∧
        (B.1 < B.2.2.1 ∧ B.2.2.1 ≤ B.2.1 ∧ w % 2 ^ (B.2.2.1 - B.1 - 1) = 0 ∧
          w.testBit (B.2.2.1 - B.1 - 1) = true) ∧
        ((cnt < 2 ∧ B.2.2.2.1 = 0) ∨
          (2 ≤ cnt ∧ B.2.2.1 < B.2.2.2.1 ∧ B.2.2.2.1 ≤ B.2.1 ∧ w.testBit (B.2.2.2.1 - B.1 - 1) = true)) ∧
        ((cnt < 3 ∧ B.2.2.2.2 = 0) ∨
          (3 ≤ cnt ∧ B.2.2.2.1 < B.2.2.2.2 ∧ B.2.2.2.2 ≤ B.2.1 ∧ w.testBit (B.2.2.2.2 - B.1 - 1) = true)) ∧
        ((U + cnt * lhi < B.1 * scale) ∨
          ((U + cnt * lhi - B.1 * scale) * lhi ^ 4 < 100 * B.1 * scale ^ 5)) ∧
        ((B.2.2.1 * scale - L) * lhi ^ 4 < 100 * B.1 * scale ^ 5) ∧
        (((if 2 ≤ cnt then B.2.2.2.1 else B.2.1) * scale - L - llo) * lhi ^ 4 <
          100 * B.2.2.1 * scale ^ 5) ∧
        (cnt < 2 ∨ (((if 3 ≤ cnt then B.2.2.2.2 else B.2.1) * scale - L - 2 * llo) * lhi ^ 4 <
          100 * B.2.2.2.1 * scale ^ 5)) ∧
        (cnt < 3 ∨ ((B.2.1 * scale - L - 3 * llo) * lhi ^ 4 < 100 * B.2.2.2.2 * scale ^ 5)) ∧
        (B.1 = gate → (U - B.1 * scale) * (logUpNum B.1) ^ 4 < 100 * B.1 * scale ^ 5 ∧
          (B.1 * scale - L) * (logUpNum B.1) ^ 4 < 100 * B.1 * scale ^ 5)))) gbase m B L U L' U' ∧ acc B.2.1 L' U')
    (fun prev L U => prev = G.2.1 ∧ L = G.2.2.2.2.1 ∧ U = G.2.2.2.2.2.1)) prev L U) G gbase m prev L U blks →
      (∀ B ∈ blks, gbase ≤ B.1 ∧ B.1 < B.2.1 ∧ B.2.1 ≤ G.2.1) →
      (L : ℝ) ≤ S * Chebyshev.theta (prev : ℝ) →
      S * Chebyshev.theta (prev : ℝ) ≤ (U : ℝ) →
      (G.2.2.2.2.1 : ℝ) ≤ S * Chebyshev.theta (G.2.1 : ℝ) ∧
        S * Chebyshev.theta (G.2.1 : ℝ) ≤ (G.2.2.2.2.2.1 : ℝ) := by
  intro prev L U blks
  induction blks generalizing prev L U with
  | nil =>
    intro hspec _ hL hU
    simp only [List.foldr] at hspec
    obtain ⟨hprev, hLf, hUf⟩ := hspec
    subst hprev
    exact ⟨by rw [← hLf]; exact hL, by rw [← hUf]; exact hU⟩
  | cons B rest ih =>
    intro hspec hbd hL hU
    simp only [List.foldr] at hspec
    obtain ⟨hprev, L', U', hbs, hrest⟩ := hspec
    subst hprev
    have hB := hbd B (by simp)
    have hst := blk_state hm hbs hB.1 hbase1 hsq hB.2.2 h8top
      (le_trans hbase1 hB.1) hB.2.1 hL hU
    have hbd' : ∀ B' ∈ rest, gbase ≤ B'.1 ∧ B'.1 < B'.2.1 ∧ B'.2.1 ≤ G.2.1 := by
      intro B' hB'
      exact hbd B' (List.mem_cons_of_mem B hB')
    exact ih B.2.1 L' U' hrest hbd' hst.1 hst.2

theorem grpSpec_range {G : Grp} {gbase m : ℕ} (hm : m = mask gbase G.2.1)
    (hbase1 : 1 ≤ gbase) (hsq : G.2.1 ≤ gbase * gbase) (h8top : G.2.1 ≤ 10 ^ 8) :
    ∀ prev L U blks, (fun (G : Grp) (gbase m prev L U : ℕ) (blks : List Blk) =>
  (blks.foldr (fun B acc => fun prev L U =>
    prev = B.1 ∧ ∃ L' U', (fun (gbase m : ℕ) (B : Blk) (L U L' U' : ℕ) => ∃ w cnt llo lhi : ℕ,
    w = m / 2 ^ (B.1 - gbase) % 2 ^ (B.2.1 - B.1) ∧
    cnt = bitCount (depthFor (B.2.1 - B.1)) w ∧
    llo = logLoNum (B.1 + 1) ∧
    lhi = logUpNum B.2.1 ∧
    L' = L + cnt * llo ∧
    U' = U + cnt * lhi ∧
    (B.1 < gate ∨
      (cnt = 0 ∧
        (B.2.1 * scale - L) * lhi ^ 4 < 100 * B.1 * scale ^ 5 ∧
        (U < B.1 * scale ∨ (U - B.1 * scale) * lhi ^ 4 < 100 * B.1 * scale ^ 5)) ∨
      (cnt ≠ 0 ∧
        (B.1 < B.2.2.1 ∧ B.2.2.1 ≤ B.2.1 ∧ w % 2 ^ (B.2.2.1 - B.1 - 1) = 0 ∧
          w.testBit (B.2.2.1 - B.1 - 1) = true) ∧
        ((cnt < 2 ∧ B.2.2.2.1 = 0) ∨
          (2 ≤ cnt ∧ B.2.2.1 < B.2.2.2.1 ∧ B.2.2.2.1 ≤ B.2.1 ∧ w.testBit (B.2.2.2.1 - B.1 - 1) = true)) ∧
        ((cnt < 3 ∧ B.2.2.2.2 = 0) ∨
          (3 ≤ cnt ∧ B.2.2.2.1 < B.2.2.2.2 ∧ B.2.2.2.2 ≤ B.2.1 ∧ w.testBit (B.2.2.2.2 - B.1 - 1) = true)) ∧
        ((U + cnt * lhi < B.1 * scale) ∨
          ((U + cnt * lhi - B.1 * scale) * lhi ^ 4 < 100 * B.1 * scale ^ 5)) ∧
        ((B.2.2.1 * scale - L) * lhi ^ 4 < 100 * B.1 * scale ^ 5) ∧
        (((if 2 ≤ cnt then B.2.2.2.1 else B.2.1) * scale - L - llo) * lhi ^ 4 <
          100 * B.2.2.1 * scale ^ 5) ∧
        (cnt < 2 ∨ (((if 3 ≤ cnt then B.2.2.2.2 else B.2.1) * scale - L - 2 * llo) * lhi ^ 4 <
          100 * B.2.2.2.1 * scale ^ 5)) ∧
        (cnt < 3 ∨ ((B.2.1 * scale - L - 3 * llo) * lhi ^ 4 < 100 * B.2.2.2.2 * scale ^ 5)) ∧
        (B.1 = gate → (U - B.1 * scale) * (logUpNum B.1) ^ 4 < 100 * B.1 * scale ^ 5 ∧
          (B.1 * scale - L) * (logUpNum B.1) ^ 4 < 100 * B.1 * scale ^ 5)))) gbase m B L U L' U' ∧ acc B.2.1 L' U')
    (fun prev L U => prev = G.2.1 ∧ L = G.2.2.2.2.1 ∧ U = G.2.2.2.2.2.1)) prev L U) G gbase m prev L U blks →
      (∀ B ∈ blks, gbase ≤ B.1 ∧ B.1 < B.2.1 ∧ B.2.1 ≤ G.2.1 ∧ gate ≤ B.1) →
      (L : ℝ) ≤ S * Chebyshev.theta (prev : ℝ) →
      S * Chebyshev.theta (prev : ℝ) ≤ (U : ℝ) →
      ((G.2.2.2.2.1 : ℝ) ≤ S * Chebyshev.theta (G.2.1 : ℝ) ∧
        S * Chebyshev.theta (G.2.1 : ℝ) ≤ (G.2.2.2.2.2.1 : ℝ)) ∧
      (∀ x : ℝ, (prev : ℝ) ≤ x → x < (G.2.1 : ℝ) →
        |Chebyshev.theta x - x| < 100 * x / (Real.log x) ^ 4) := by
  intro prev L U blks
  induction blks generalizing prev L U with
  | nil =>
    intro hspec _ hL hU
    simp only [List.foldr] at hspec
    obtain ⟨hprev, hLf, hUf⟩ := hspec
    subst hprev
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [← hLf]; exact hL
    · rw [← hUf]; exact hU
    · intro x hx1 hx2
      exact absurd hx2 (not_lt_of_ge hx1)
  | cons B rest ih =>
    intro hspec hbd hL hU
    simp only [List.foldr] at hspec
    obtain ⟨hprev, L', U', hbs, hrest⟩ := hspec
    subst hprev
    have hB := hbd B (by simp)
    have hst := blk_state hm hbs hB.1 hbase1 hsq hB.2.2.1 h8top
      (le_trans hbase1 hB.1) hB.2.1 hL hU
    have hbd' : ∀ B' ∈ rest,
        gbase ≤ B'.1 ∧ B'.1 < B'.2.1 ∧ B'.2.1 ≤ G.2.1 ∧ gate ≤ B'.1 := by
      intro B' hB'
      exact hbd B' (List.mem_cons_of_mem B hB')
    have hrec := ih B.2.1 L' U' hrest hbd' hst.1 hst.2
    refine ⟨hrec.1, ?_⟩
    intro x hx1 hx2
    by_cases hxb : x ≤ (B.2.1 : ℝ)
    · exact blk_range hm hbs hB.1 hbase1 hsq hB.2.2.1 h8top hB.2.2.2 hB.2.1 hL hst.2
        x hx1 hxb
    · have hbx : (B.2.1 : ℝ) ≤ x := le_of_lt (not_le.mp hxb)
      exact hrec.2 x hbx hx2

theorem grp_state_of (G : Grp) (hOK : grpOK G = true) (hwf : grpWF G = true)
    (hL : (G.2.2.1 : ℝ) ≤ S * Chebyshev.theta (G.1 : ℝ))
    (hU : S * Chebyshev.theta (G.1 : ℝ) ≤ (G.2.2.2.1 : ℝ)) :
    (G.2.2.2.2.1 : ℝ) ≤ S * Chebyshev.theta (G.2.1 : ℝ) ∧
      S * Chebyshev.theta (G.2.1 : ℝ) ≤ (G.2.2.2.2.2.1 : ℝ) := by
  have hP := grpWF_spec hwf
  exact grpSpec_state rfl hP.1.1 hP.1.2.2.2.1 hP.1.2.2.2.2
    G.1 G.2.2.1 G.2.2.2.1 G.2.2.2.2.2.2 (grpOK_spec hOK) hP.2 hL hU

theorem grp_range_of (G : Grp) (hOK : grpOK G = true) (hwf : grpWF G = true)
    (hL : (G.2.2.1 : ℝ) ≤ S * Chebyshev.theta (G.1 : ℝ))
    (hU : S * Chebyshev.theta (G.1 : ℝ) ≤ (G.2.2.2.1 : ℝ))
    (hgate : gate ≤ G.1) :
    ((G.2.2.2.2.1 : ℝ) ≤ S * Chebyshev.theta (G.2.1 : ℝ) ∧
      S * Chebyshev.theta (G.2.1 : ℝ) ≤ (G.2.2.2.2.2.1 : ℝ)) ∧
    (∀ x : ℝ, (G.1 : ℝ) ≤ x → x < (G.2.1 : ℝ) →
      |Chebyshev.theta x - x| < 100 * x / (Real.log x) ^ 4) := by
  have hP := grpWF_spec hwf
  refine grpSpec_range rfl hP.1.1 hP.1.2.2.2.1 hP.1.2.2.2.2
    G.1 G.2.2.1 G.2.2.2.1 G.2.2.2.2.2.2 (grpOK_spec hOK) ?_ hL hU
  intro B hB
  exact ⟨(hP.2 B hB).1, (hP.2 B hB).2.1, (hP.2 B hB).2.2, le_trans hgate (hP.2 B hB).1⟩

end AxlerChain

end LeanLab.Ported.Prove2Me.Task666
