/-
P0076, Section 4, Proposition 4.1 v, page 16 after display 4.5.
Split of the HARD leaf `enveloping_v_decay` of EnvelopingFourierSplit.lean into an exact
local evaluation bound, the Ramare and Ruzsa bound for the Selberg quadratic form twisted
at q, and a proved divisor type bound K to the omega of q at most C of epsilon times q to
the epsilon. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.EnvelopingFourierSplit

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- `‖eC x‖ = 1`. -/
private theorem efsv_eC_norm (x : ℝ) : ‖eC x‖ = 1 := by
  simp [eC, Complex.norm_exp]

/-- `eC` of a fraction depends only on the residue of the numerator. -/
private theorem efsv_eC_mod (q a r : ℕ) (hq : q ≠ 0) :
    eC ((a : ℝ) * (r : ℝ) / (q : ℝ)) = eC ((a : ℝ) * ((r % q : ℕ) : ℝ) / (q : ℝ)) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hcast : (r : ℝ) = ((r % q : ℕ) : ℝ) + (q : ℝ) * ((r / q : ℕ) : ℝ) := by
    have h : (((q * (r / q) + r % q : ℕ)) : ℝ) = (r : ℝ) := by
      rw [Nat.div_add_mod r q]
    push_cast at h
    linarith [h]
  have key : (a : ℝ) * (r : ℝ) / (q : ℝ) =
      (a : ℝ) * ((r % q : ℕ) : ℝ) / (q : ℝ) + ((a * (r / q) : ℕ) : ℝ) := by
    have hexp : (a : ℝ) * (r : ℝ) =
        (a : ℝ) * ((r % q : ℕ) : ℝ) + (a : ℝ) * ((r / q : ℕ) : ℝ) * (q : ℝ) := by
      rw [hcast]; ring
    have hL : (a : ℝ) * (r : ℝ) / (q : ℝ) * (q : ℝ) = (a : ℝ) * (r : ℝ) := by
      rw [div_mul_cancel₀ _ hq']
    have hR : ((a : ℝ) * ((r % q : ℕ) : ℝ) / (q : ℝ) + ((a * (r / q) : ℕ) : ℝ)) * (q : ℝ)
        = (a : ℝ) * (r : ℝ) := by
      rw [add_mul, div_mul_cancel₀ _ hq', hexp]
      push_cast
      ring
    exact mul_right_cancel₀ hq' (by rw [hL, hR])
  rw [key, efs_eC_add]
  have hone : eC ((a * (r / q) : ℕ) : ℝ) = 1 := by
    rw [show ((a * (r / q) : ℕ) : ℝ) = ((((a * (r / q) : ℕ)) : ℤ) : ℝ) from
      (Int.cast_natCast (R := ℝ) (a * (r / q))).symm]
    exact efs_eC_int _
  rw [hone, mul_one]

private theorem efsv_sifted_mul {w : ℕ} {m : ℤ} {q M : ℕ} (hsq : Squarefree q) (hsM : Squarefree M)
    (hc : Nat.Coprime q M) :
    EnvelopingSifted w (q * M) m ↔ EnvelopingSifted w q m ∧ EnvelopingSifted w M m := by
  unfold EnvelopingSifted
  have hsqm : Squarefree (q * M) ↔ (Nat.Coprime q M ∧ Squarefree q ∧ Squarefree M) :=
    Nat.squarefree_mul_iff
  rw [Nat.Coprime.primeFactors_mul hc, Finset.forall_mem_union, hsqm]
  constructor
  · rintro ⟨⟨-, hq, hM⟩, h1, h2⟩
    exact ⟨⟨hsq, h1⟩, ⟨hsM, h2⟩⟩
  · rintro ⟨⟨hq, h1⟩, ⟨hM, h2⟩⟩
    exact ⟨⟨hc, hq, hM⟩, h1, h2⟩

/-- Chinese remainder theorem for sums of a product of complex terms over a full period. -/
private theorem efsv_crt_sum (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (h : Nat.Coprime m n) (f g : ℕ → ℂ) :
    ∑ r ∈ range (m * n), f (r % m) * g (r % n) =
      (∑ x ∈ range m, f x) * (∑ y ∈ range n, g y) := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  apply sum_nbij (fun r => (r % m, r % n))
  · intro r _
    simp only [mem_product, mem_range]
    exact ⟨Nat.mod_lt r hm, Nat.mod_lt r hn⟩
  · intro r1 h1 r2 h2 heq
    simp only [Prod.mk.injEq] at heq
    have hmod := (Nat.modEq_and_modEq_iff_modEq_mul h).mp ⟨heq.1, heq.2⟩
    have e1 := Nat.mod_eq_of_lt (mem_range.mp (mem_coe.mp h1))
    have e2 := Nat.mod_eq_of_lt (mem_range.mp (mem_coe.mp h2))
    unfold Nat.ModEq at hmod
    rw [e1, e2] at hmod
    exact hmod
  · rintro ⟨x, y⟩ hxy
    simp only [coe_product, Set.mem_prod, mem_coe, mem_range] at hxy
    obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder h x y
    refine ⟨k % (m * n), ?_, ?_⟩
    · exact mem_coe.mpr (mem_range.mpr (Nat.mod_lt _ (Nat.mul_pos hm hn)))
    · simp only [Prod.mk.injEq]
      constructor
      · rw [Nat.mod_mod_of_dvd _ (dvd_mul_right m n)]
        unfold Nat.ModEq at hk1
        rw [hk1, Nat.mod_eq_of_lt hxy.1]
      · rw [Nat.mod_mod_of_dvd _ (dvd_mul_left n m)]
        unfold Nat.ModEq at hk2
        rw [hk2, Nat.mod_eq_of_lt hxy.2]
  · intro r _
    rfl

/-- The two indicator factors multiply to the indicator of the lcm. -/
private theorem efsv_ind_lcm {w J : ℕ} (hw : 5 ≤ w) {z : ℝ} {d1 d2 : ℕ} (b : ℤ) {s : ℕ}
    (hd1 : d1 ∣ envelopingPrimeProduct w z) (hd2 : d2 ∣ envelopingPrimeProduct w z) :
    (((if EnvelopingSifted w d1 (WW J w * (s : ℤ) + b) then (1 : ℝ) else 0)) : ℂ) *
        (((if EnvelopingSifted w d2 (WW J w * (s : ℤ) + b) then (1 : ℝ) else 0)) : ℂ) =
      (((if EnvelopingSifted w (Nat.lcm d1 d2) (WW J w * (s : ℤ) + b) then (1 : ℝ) else 0)) : ℂ) := by
  have hiff := efs_sifted_lcm hw hd1 hd2 (WW J w * (s : ℤ) + b)
  by_cases h1 : EnvelopingSifted w d1 (WW J w * (s : ℤ) + b)
  · by_cases h2 : EnvelopingSifted w d2 (WW J w * (s : ℤ) + b)
    · have hL := hiff.mp ⟨h1, h2⟩
      rw [if_pos h1, if_pos h2, if_pos hL]
      norm_num
    · have hL : ¬ EnvelopingSifted w (Nat.lcm d1 d2) (WW J w * (s : ℤ) + b) :=
        fun h => h2 (hiff.mpr h).2
      rw [if_pos h1, if_neg h2, if_neg hL]
      norm_num
  · have hL : ¬ EnvelopingSifted w (Nat.lcm d1 d2) (WW J w * (s : ℤ) + b) :=
      fun h => h1 (hiff.mpr h).1
    rw [if_neg h1, if_neg hL]
    norm_num


/-- One full period of the twisted count factors by the Chinese remainder theorem. -/
private theorem efsv_twist_period {J w : ℕ} (hw : 5 ≤ w) (b : ℤ) (z : ℝ) {q L : ℕ}
    (hqP : q ∣ envelopingPrimeProduct w z) (hL : L ∣ envelopingPrimeProduct w z)
    (hqL : q ∣ L) (a : ℕ) :
    ∑ r ∈ range L,
        ((((if EnvelopingSifted w L (WW J w * (r : ℤ) + b) then (1 : ℝ) else 0)) : ℂ) * eC ((a : ℝ) * (r : ℝ) / (q : ℝ))) =
      (∑ x ∈ range q,
        ((((if EnvelopingSifted w q (WW J w * (x : ℤ) + b) then (1 : ℝ) else 0)) : ℂ) * eC ((a : ℝ) * (x : ℝ) / (q : ℝ)))) *
        (((L / q : ℕ) * envelopingDensity w (L / q) : ℝ) : ℂ) := by
  have hP0 : envelopingPrimeProduct w z ≠ 0 := envelopingPrimeProduct_ne_zero w z
  have hqpos : 0 < q := Nat.pos_of_dvd_of_pos hqP (Nat.pos_of_ne_zero hP0)
  have hLpos : 0 < L := Nat.pos_of_dvd_of_pos hL (Nat.pos_of_ne_zero hP0)
  have hqL' := hqL
  obtain ⟨Mm, hMm⟩ := hqL'
  have hMpos : 0 < Mm := Nat.pos_of_mul_pos_left (hMm ▸ hLpos)
  have hsqL : Squarefree (q * Mm) := hMm ▸ (enveloping_divisor_support (J := J) hw hL).1
  have hsplit := Nat.squarefree_mul_iff.mp hsqL
  have hc : Nat.Coprime q Mm := hsplit.1
  have hsqQ : Squarefree q := hsplit.2.1
  have hsqMm : Squarefree Mm := hsplit.2.2
  have hLq : L / q = Mm := by
    refine Nat.eq_of_mul_eq_mul_right hqpos ?_
    rw [Nat.div_mul_cancel hqL, hMm, Nat.mul_comm]
  have hpt : ∀ r : ℕ,
      ((((if EnvelopingSifted w (q * Mm) (WW J w * (r : ℤ) + b) then (1 : ℝ) else 0)) : ℂ) * eC ((a : ℝ) * (r : ℝ) / (q : ℝ))) =
        (((((if EnvelopingSifted w q (WW J w * (((r % q : ℕ)) : ℤ) + b) then (1 : ℝ) else 0)) : ℂ) * eC ((a : ℝ) * ((r % q : ℕ) : ℝ) / (q : ℝ))) *
          ((((if EnvelopingSifted w Mm (WW J w * (((r % Mm : ℕ)) : ℤ) + b) then (1 : ℝ) else 0)) : ℂ))) := by
    intro r
    rw [efsv_eC_mod q a r hqpos.ne']
    have hs : ((if EnvelopingSifted w (q * Mm) (WW J w * (r : ℤ) + b) then (1 : ℝ) else 0) : ℂ) =
        ((if EnvelopingSifted w q (WW J w * (r : ℤ) + b) then (1 : ℝ) else 0) : ℂ) *
          ((if EnvelopingSifted w Mm (WW J w * (r : ℤ) + b) then (1 : ℝ) else 0) : ℂ) := by
      rw [efsv_sifted_mul (m := WW J w * (r : ℤ) + b) hsqQ hsqMm hc]
      by_cases h1 : EnvelopingSifted w q (WW J w * (r : ℤ) + b)
      · by_cases h2 : EnvelopingSifted w Mm (WW J w * (r : ℤ) + b)
        · rw [if_pos ⟨h1, h2⟩, if_pos h1, if_pos h2]; norm_num
        · rw [if_neg (fun h => h2 h.2), if_pos h1, if_neg h2]; norm_num
      · rw [if_neg (fun h => h1 h.1), if_neg h1]; norm_num
    have e1 : ((if EnvelopingSifted w q (WW J w * (r : ℤ) + b) then (1 : ℝ) else 0) : ℂ) =
        ((if EnvelopingSifted w q (WW J w * ((r % q : ℕ) : ℤ) + b) then (1 : ℝ) else 0) : ℂ) := by
      have hs1 := efs_sifted_shift w q (WW J w) b q (r % q) (r / q) dvd_rfl
      rw [Nat.div_add_mod] at hs1
      rw [hs1]
    have e2 : ((if EnvelopingSifted w Mm (WW J w * (r : ℤ) + b) then (1 : ℝ) else 0) : ℂ) =
        ((if EnvelopingSifted w Mm (WW J w * ((r % Mm : ℕ) : ℤ) + b) then (1 : ℝ) else 0) : ℂ) := by
      have hs2 := efs_sifted_shift w Mm (WW J w) b Mm (r % Mm) (r / Mm) dvd_rfl
      rw [Nat.div_add_mod] at hs2
      rw [hs2]
    conv_lhs => rw [hs, e1, e2]
    ring
  have hMmP : Mm ∣ envelopingPrimeProduct w z := dvd_trans (dvd_mul_left Mm q) (hMm ▸ hL)
  have hcount := efs_count_period (J := J) hw b z hMmP
  have hg : (∑ y ∈ range Mm, (((if EnvelopingSifted w Mm (WW J w * (y : ℤ) + b) then (1 : ℝ) else 0)) : ℂ)) = (((Mm : ℝ) * envelopingDensity w Mm : ℝ) : ℂ) := by
    have h1 : (∑ y ∈ range Mm, (((if EnvelopingSifted w Mm (WW J w * (y : ℤ) + b) then (1 : ℝ) else 0)) : ℂ)) =
        (((∑ y ∈ range Mm,
          (if EnvelopingSifted w Mm (WW J w * (y : ℤ) + b) then (1 : ℝ) else 0)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro y _
      by_cases h : EnvelopingSifted w Mm (WW J w * (y : ℤ) + b)
      · simp [h]
      · simp [h]
    rw [h1, hcount]
  have hsum : (∑ r ∈ range (q * Mm),
      ((((if EnvelopingSifted w (q * Mm) (WW J w * (r : ℤ) + b) then (1 : ℝ) else 0)) : ℂ) * eC ((a : ℝ) * (r : ℝ) / (q : ℝ)))) =
      ∑ r ∈ range (q * Mm),
        (((((if EnvelopingSifted w q (WW J w * (((r % q : ℕ)) : ℤ) + b) then (1 : ℝ) else 0)) : ℂ) * eC ((a : ℝ) * ((r % q : ℕ) : ℝ) / (q : ℝ))) *
          ((((if EnvelopingSifted w Mm (WW J w * (((r % Mm : ℕ)) : ℤ) + b) then (1 : ℝ) else 0)) : ℂ))) :=
    Finset.sum_congr rfl (fun r _ => hpt r)
  rw [hLq, hMm, hsum]
  rw [efsv_crt_sum q Mm hqpos hMpos hc
      (fun x => ((((if EnvelopingSifted w q (WW J w * (x : ℤ) + b) then (1 : ℝ) else 0)) : ℂ) * eC ((a : ℝ) * (x : ℝ) / (q : ℝ))))
      (fun y => ((((if EnvelopingSifted w Mm (WW J w * (y : ℤ) + b) then (1 : ℝ) else 0)) : ℂ)))]
  rw [hg]
  try push_cast
  try ring


/-- The twisted count over the whole range: `P` is a whole number of periods. -/
private theorem efsv_twist_range {J w : ℕ} (hw : 5 ≤ w) (b : ℤ) (z : ℝ) {q L : ℕ}
    (hqP : q ∣ envelopingPrimeProduct w z) (hL : L ∣ envelopingPrimeProduct w z)
    (hqL : q ∣ L) (a : ℕ) :
    ∑ s ∈ range (envelopingPrimeProduct w z),
        ((((if EnvelopingSifted w L (WW J w * (s : ℤ) + b) then (1 : ℝ) else 0)) : ℂ) * eC ((a : ℝ) * (s : ℝ) / (q : ℝ))) =
      (((envelopingPrimeProduct w z) / L : ℕ) : ℂ) *
        ((∑ x ∈ range q,
          ((((if EnvelopingSifted w q (WW J w * (x : ℤ) + b) then (1 : ℝ) else 0)) : ℂ) * eC ((a : ℝ) * (x : ℝ) / (q : ℝ)))) *
          (((L / q : ℕ) * envelopingDensity w (L / q) : ℝ) : ℂ)) := by
  have hP0 : envelopingPrimeProduct w z ≠ 0 := envelopingPrimeProduct_ne_zero w z
  have hLpos : 0 < L := Nat.pos_of_dvd_of_pos hL (Nat.pos_of_ne_zero hP0)
  have hqpos : 0 < q := Nat.pos_of_dvd_of_pos hqP (Nat.pos_of_ne_zero hP0)
  have hLc := hL
  obtain ⟨m, hm⟩ := hLc
  have hPL : L * m / L = m := Nat.mul_div_right m hLpos
  have hper : ∀ (j r : ℕ),
      ((((if EnvelopingSifted w L (WW J w * (((L * j + r : ℕ)) : ℤ) + b) then (1 : ℝ) else 0)) : ℂ) * eC ((a : ℝ) * ((L * j + r : ℕ) : ℝ) / (q : ℝ))) =
        (((((if EnvelopingSifted w L (WW J w * (r : ℤ) + b) then (1 : ℝ) else 0)) : ℂ) * eC ((a : ℝ) * (r : ℝ) / (q : ℝ))) *
          eC ((a : ℝ) * ((L * j : ℕ) : ℝ) / (q : ℝ))) := by
    intro j r
    have hs : ((if EnvelopingSifted w L (WW J w * ((L * j + r : ℕ) : ℤ) + b) then (1 : ℝ) else 0) : ℂ) =
        ((if EnvelopingSifted w L (WW J w * (r : ℤ) + b) then (1 : ℝ) else 0) : ℂ) := by
      have hh := efs_sifted_shift w L (WW J w) b L r j dvd_rfl
      rw [hh]
    rw [hs]
    rw [show (a : ℝ) * ((L * j + r : ℕ) : ℝ) / (q : ℝ)
        = (a : ℝ) * (r : ℝ) / (q : ℝ) + (a : ℝ) * ((L * j : ℕ) : ℝ) / (q : ℝ) by
      push_cast; ring]
    rw [efs_eC_add]
    ring
  have h1 : ∀ j : ℕ, eC ((a : ℝ) * ((L * j : ℕ) : ℝ) / (q : ℝ)) = 1 := by
    intro j
    obtain ⟨c, hc⟩ := dvd_mul_of_dvd_left hqL j
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hqpos.ne'
    have hkey : (a : ℝ) * ((L * j : ℕ) : ℝ) / (q : ℝ) = (((a * c : ℕ) : ℤ) : ℝ) := by
      rw [hc]; push_cast; field_simp
    rw [hkey, efs_eC_int]
  rw [hm, efs_sum_range_mul]
  rw [Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun r _ => by rw [hper j r, h1 j, mul_one]))]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [efsv_twist_period (J := J) hw b z hqP hL hqL a, hPL]


/-- LEAF: Proposition 4.1 v, page 16, display 4.5 before the character sum is bounded,
class MEDIUM. Expanding the square in display 4.3, the coefficient at a over q is G 1 of z
times the sum over d1, d2 dividing P of z of rho_d1 rho_d2 times the mean over one period
lcm d1 d2 of the indicator of A of lcm d1 d2 against e of a r over q. This mean vanishes
unless q divides lcm d1 d2, as in reference 18 formula 4.1.13; when it does, the Chinese
remainder theorem splits it into g of lcm d1 d2 over q times the local sum at q, and the
local sum at q has norm at most g of q, the trivial bound of reference 18 formula 4.1.17. -/
theorem vdecay_local_eval {J w : ℕ} (hw : 5 ≤ w) (b : ℤ) (M : ℕ) {q a : ℕ}
    (hqP : q ∣ envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10)))
    (ha : a < q) (hcop : Nat.Coprime a q) :
    ‖envelopingVraw w (WW J w) b M q a‖ ≤
      envelopingDensity w q *
        |envelopingG w 1 ((M : ℝ) ^ ((1 : ℝ) / 10)) *
          ∑ d1 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors,
            ∑ d2 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors,
              if q ∣ Nat.lcm d1 d2 then
                envelopingRho w d1 ((M : ℝ) ^ ((1 : ℝ) / 10)) *
                  envelopingRho w d2 ((M : ℝ) ^ ((1 : ℝ) / 10)) *
                    envelopingDensity w (Nat.lcm d1 d2 / q)
              else 0| := by
  have hP0 : envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10)) ≠ 0 := envelopingPrimeProduct_ne_zero w ((M : ℝ) ^ ((1 : ℝ) / 10))
  have hqpos : 0 < q := Nat.pos_of_dvd_of_pos hqP (Nat.pos_of_ne_zero hP0)
  have hq0c : (q : ℂ) ≠ 0 := by exact_mod_cast hqpos.ne'
  -- (1) the twisted sum over one full range, in the form the CRT produces
  have hstep : ∀ d1 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors, ∀ d2 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors,
      (∑ s ∈ range (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))), ((((if EnvelopingSifted w d1 (WW J w * (s : ℤ) + b) then (1 : ℝ) else 0)) : ℂ) * eC ((a : ℝ) * (s : ℝ) / (q : ℝ))) * (((if EnvelopingSifted w d2 (WW J w * (s : ℤ) + b) then (1 : ℝ) else 0)) : ℂ))
        = if q ∣ Nat.lcm d1 d2 then
            (((envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))) / Nat.lcm d1 d2 : ℕ) : ℂ) * (∑ x ∈ range q, (((if EnvelopingSifted w q (WW J w * (x : ℤ) + b) then (1 : ℝ) else 0)) : ℂ) * eC ((a : ℝ) * (x : ℝ) / (q : ℝ))) *
              (((Nat.lcm d1 d2 / q : ℕ) * envelopingDensity w (Nat.lcm d1 d2 / q) : ℝ) : ℂ)
          else 0 := by
    intro d1 hd1 d2 hd2
    have hd1P : d1 ∣ envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10)) := Nat.dvd_of_mem_divisors hd1
    have hd2P : d2 ∣ envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10)) := Nat.dvd_of_mem_divisors hd2
    have hLP : Nat.lcm d1 d2 ∣ envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10)) := Nat.lcm_dvd hd1P hd2P
    have hconv : ∀ s : ℕ,
        (((((if EnvelopingSifted w d1 (WW J w * (s : ℤ) + b) then (1 : ℝ) else 0)) : ℂ) * eC ((a : ℝ) * (s : ℝ) / (q : ℝ))) * (((if EnvelopingSifted w d2 (WW J w * (s : ℤ) + b) then (1 : ℝ) else 0)) : ℂ)) =
          ((((if EnvelopingSifted w (Nat.lcm d1 d2) (WW J w * (s : ℤ) + b) then (1 : ℝ) else 0)) : ℂ) * eC ((a : ℝ) * (s : ℝ) / (q : ℝ))) := by
      intro s
      have hi := efsv_ind_lcm (J := J) hw (z := ((M : ℝ) ^ ((1 : ℝ) / 10))) b (s := s) hd1P hd2P
      rw [← hi]
      ring
    rw [Finset.sum_congr rfl (fun s _ => hconv s)]
    by_cases hqL : q ∣ Nat.lcm d1 d2
    · rw [if_pos hqL]
      rw [efsv_twist_range (J := J) hw b ((M : ℝ) ^ ((1 : ℝ) / 10)) hqP hLP hqL a]
      ring
    · rw [if_neg hqL]
      exact efs_periodic_vanish (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))) (Nat.lcm d1 d2) q a hP0 hLP hqP hqL hcop
        (fun s => (((if EnvelopingSifted w (Nat.lcm d1 d2) (WW J w * (s : ℤ) + b) then (1 : ℝ) else 0)) : ℂ))
        (fun j r => by
          simp only [efs_sifted_shift w (Nat.lcm d1 d2) (WW J w) b (Nat.lcm d1 d2) r j dvd_rfl])
  -- (2) expanding the square inside the Fourier coefficient
  have hFs : ∀ s : ℕ, ((envelopingF w (WW J w) b M s : ℝ) : ℂ) =
      ∑ d1 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors, ∑ d2 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors,
        (((envelopingG w 1 ((M : ℝ) ^ ((1 : ℝ) / 10)) * envelopingRho w d1 ((M : ℝ) ^ ((1 : ℝ) / 10)) * envelopingRho w d2 ((M : ℝ) ^ ((1 : ℝ) / 10)) : ℝ) : ℂ) *
          (((((if EnvelopingSifted w d1 (WW J w * (s : ℤ) + b) then (1 : ℝ) else 0)) : ℂ)) * (((if EnvelopingSifted w d2 (WW J w * (s : ℤ) + b) then (1 : ℝ) else 0)) : ℂ))) := by
    intro s
    rw [efs_F_expand, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro d1 _
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro d2 _
    by_cases h1 : EnvelopingSifted w d1 (WW J w * (s : ℤ) + b)
    · by_cases h2 : EnvelopingSifted w d2 (WW J w * (s : ℤ) + b)
      · simp only [h1, h2, if_true]
        push_cast
        ring
      · simp only [h1, h2, if_true, if_false]
        simp
    · simp only [h1, if_false]
      simp
  -- (3) the local factor `(P/L)(L/q)` is `P/q`
  have hfac : ∀ d1 d2 : ℕ, q ∣ Nat.lcm d1 d2 → Nat.lcm d1 d2 ∣ envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10)) →
      (((envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))) / Nat.lcm d1 d2 : ℕ) : ℂ) * (((Nat.lcm d1 d2 / q : ℕ)) : ℂ) =
        (((envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))) / q : ℕ) : ℂ) := by
    intro d1 d2 hqL hLP
    have hkey : ((envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))) / Nat.lcm d1 d2) * (Nat.lcm d1 d2 / q) = (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))) / q := by
      refine Nat.eq_of_mul_eq_mul_right hqpos ?_
      have h1' : (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))) / Nat.lcm d1 d2 * Nat.lcm d1 d2 = envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10)) := Nat.div_mul_cancel hLP
      have h2' : Nat.lcm d1 d2 / q * q = Nat.lcm d1 d2 := Nat.div_mul_cancel hqL
      calc ((envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))) / Nat.lcm d1 d2 * (Nat.lcm d1 d2 / q)) * q
          = (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))) / Nat.lcm d1 d2 * (Nat.lcm d1 d2 / q * q) := by ring
        _ = (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))) / Nat.lcm d1 d2 * Nat.lcm d1 d2 := by rw [h2']
        _ = envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10)) := h1'
        _ = (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))) / q * q := (Nat.div_mul_cancel hqP).symm
    rw [← hkey]
    push_cast
    ring
  -- (4) each pair contributes the exact multiple of the local sum
  have hpair : ∀ d1 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors, ∀ d2 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors,
      ((envelopingG w 1 ((M : ℝ) ^ ((1 : ℝ) / 10)) * envelopingRho w d1 ((M : ℝ) ^ ((1 : ℝ) / 10)) * envelopingRho w d2 ((M : ℝ) ^ ((1 : ℝ) / 10)) : ℝ) : ℂ) *
          (if q ∣ Nat.lcm d1 d2 then
            (((envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))) / Nat.lcm d1 d2 : ℕ) : ℂ) * (∑ x ∈ range q, (((if EnvelopingSifted w q (WW J w * (x : ℤ) + b) then (1 : ℝ) else 0)) : ℂ) * eC ((a : ℝ) * (x : ℝ) / (q : ℝ))) *
              (((Nat.lcm d1 d2 / q : ℕ) * envelopingDensity w (Nat.lcm d1 d2 / q) : ℝ) : ℂ)
          else 0)
        = ((∑ x ∈ range q, (((if EnvelopingSifted w q (WW J w * (x : ℤ) + b) then (1 : ℝ) else 0)) : ℂ) * eC ((a : ℝ) * (x : ℝ) / (q : ℝ))) * ((((envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))) / q : ℕ)) : ℂ)) *
            (((envelopingG w 1 ((M : ℝ) ^ ((1 : ℝ) / 10)) * (if q ∣ Nat.lcm d1 d2 then
              envelopingRho w d1 ((M : ℝ) ^ ((1 : ℝ) / 10)) * envelopingRho w d2 ((M : ℝ) ^ ((1 : ℝ) / 10)) * envelopingDensity w (Nat.lcm d1 d2 / q) else 0)) : ℝ) : ℂ) := by
    intro d1 hd1 d2 hd2
    have hLP : Nat.lcm d1 d2 ∣ envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10)) :=
      Nat.lcm_dvd (Nat.dvd_of_mem_divisors hd1) (Nat.dvd_of_mem_divisors hd2)
    by_cases hqL : q ∣ Nat.lcm d1 d2
    · simp only [hqL, if_true]
      have hf := hfac d1 d2 hqL hLP
      calc ((envelopingG w 1 ((M : ℝ) ^ ((1 : ℝ) / 10)) * envelopingRho w d1 ((M : ℝ) ^ ((1 : ℝ) / 10)) * envelopingRho w d2 ((M : ℝ) ^ ((1 : ℝ) / 10)) : ℝ) : ℂ) *
            ((((envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))) / Nat.lcm d1 d2 : ℕ) : ℂ) * (∑ x ∈ range q, (((if EnvelopingSifted w q (WW J w * (x : ℤ) + b) then (1 : ℝ) else 0)) : ℂ) * eC ((a : ℝ) * (x : ℝ) / (q : ℝ))) *
              (((Nat.lcm d1 d2 / q : ℕ) * envelopingDensity w (Nat.lcm d1 d2 / q) : ℝ) : ℂ))
          = ((∑ x ∈ range q, (((if EnvelopingSifted w q (WW J w * (x : ℤ) + b) then (1 : ℝ) else 0)) : ℂ) * eC ((a : ℝ) * (x : ℝ) / (q : ℝ))) * ((((envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))) / Nat.lcm d1 d2 : ℕ) : ℂ) * ((Nat.lcm d1 d2 / q : ℕ) : ℂ))) *
              (((envelopingG w 1 ((M : ℝ) ^ ((1 : ℝ) / 10)) * (envelopingRho w d1 ((M : ℝ) ^ ((1 : ℝ) / 10)) * envelopingRho w d2 ((M : ℝ) ^ ((1 : ℝ) / 10)) * envelopingDensity w (Nat.lcm d1 d2 / q))) : ℝ) : ℂ) := by
            push_cast
            ring
        _ = ((∑ x ∈ range q, (((if EnvelopingSifted w q (WW J w * (x : ℤ) + b) then (1 : ℝ) else 0)) : ℂ) * eC ((a : ℝ) * (x : ℝ) / (q : ℝ))) * (((envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))) / q : ℕ) : ℂ)) *
              (((envelopingG w 1 ((M : ℝ) ^ ((1 : ℝ) / 10)) * (envelopingRho w d1 ((M : ℝ) ^ ((1 : ℝ) / 10)) * envelopingRho w d2 ((M : ℝ) ^ ((1 : ℝ) / 10)) * envelopingDensity w (Nat.lcm d1 d2 / q))) : ℝ) : ℂ) := by
            rw [hf]
    · simp only [hqL, if_false]
      simp
  -- (5) the expansion of the Fourier coefficient, coefficient by coefficient
  have hcore : (∑ s ∈ range (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))), ((envelopingF w (WW J w) b M s : ℝ) : ℂ) *
        eC ((a : ℝ) * (s : ℝ) / (q : ℝ))) =
      ∑ d1 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors, ∑ d2 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors,
        ((envelopingG w 1 ((M : ℝ) ^ ((1 : ℝ) / 10)) * envelopingRho w d1 ((M : ℝ) ^ ((1 : ℝ) / 10)) * envelopingRho w d2 ((M : ℝ) ^ ((1 : ℝ) / 10)) : ℝ) : ℂ) *
          (∑ s ∈ range (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))), ((((if EnvelopingSifted w d1 (WW J w * (s : ℤ) + b) then (1 : ℝ) else 0)) : ℂ) * eC ((a : ℝ) * (s : ℝ) / (q : ℝ))) * (((if EnvelopingSifted w d2 (WW J w * (s : ℤ) + b) then (1 : ℝ) else 0)) : ℂ)) := by
    simp only [hFs]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d1 _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d2 _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring
  have hinner : (∑ d1 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors, ∑ d2 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors,
        ((envelopingG w 1 ((M : ℝ) ^ ((1 : ℝ) / 10)) * envelopingRho w d1 ((M : ℝ) ^ ((1 : ℝ) / 10)) * envelopingRho w d2 ((M : ℝ) ^ ((1 : ℝ) / 10)) : ℝ) : ℂ) *
          (∑ s ∈ range (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))), ((((if EnvelopingSifted w d1 (WW J w * (s : ℤ) + b) then (1 : ℝ) else 0)) : ℂ) * eC ((a : ℝ) * (s : ℝ) / (q : ℝ))) * (((if EnvelopingSifted w d2 (WW J w * (s : ℤ) + b) then (1 : ℝ) else 0)) : ℂ)))
      = ((∑ x ∈ range q, (((if EnvelopingSifted w q (WW J w * (x : ℤ) + b) then (1 : ℝ) else 0)) : ℂ) * eC ((a : ℝ) * (x : ℝ) / (q : ℝ))) * ((((envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))) / q : ℕ)) : ℂ)) *
          ((envelopingG w 1 ((M : ℝ) ^ ((1 : ℝ) / 10)) : ℂ) * (((∑ d1 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors, ∑ d2 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors,
        if q ∣ Nat.lcm d1 d2 then envelopingRho w d1 ((M : ℝ) ^ ((1 : ℝ) / 10)) * envelopingRho w d2 ((M : ℝ) ^ ((1 : ℝ) / 10)) *
          envelopingDensity w (Nat.lcm d1 d2 / q) else 0) : ℝ) : ℂ)) := by
    have hSs : ((envelopingG w 1 ((M : ℝ) ^ ((1 : ℝ) / 10)) : ℂ) * (((∑ d1 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors, ∑ d2 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors,
        if q ∣ Nat.lcm d1 d2 then envelopingRho w d1 ((M : ℝ) ^ ((1 : ℝ) / 10)) * envelopingRho w d2 ((M : ℝ) ^ ((1 : ℝ) / 10)) *
          envelopingDensity w (Nat.lcm d1 d2 / q) else 0) : ℝ) : ℂ)) =
        ∑ d1 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors, ∑ d2 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors,
          (((envelopingG w 1 ((M : ℝ) ^ ((1 : ℝ) / 10)) * (if q ∣ Nat.lcm d1 d2 then
            envelopingRho w d1 ((M : ℝ) ^ ((1 : ℝ) / 10)) * envelopingRho w d2 ((M : ℝ) ^ ((1 : ℝ) / 10)) * envelopingDensity w (Nat.lcm d1 d2 / q) else 0)) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Finset.mul_sum, Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro d1 _
      rw [Finset.mul_sum, Complex.ofReal_sum]
    rw [hSs]
    have h1 : (∑ d1 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors, ∑ d2 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors,
        ((envelopingG w 1 ((M : ℝ) ^ ((1 : ℝ) / 10)) * envelopingRho w d1 ((M : ℝ) ^ ((1 : ℝ) / 10)) * envelopingRho w d2 ((M : ℝ) ^ ((1 : ℝ) / 10)) : ℝ) : ℂ) *
          (∑ s ∈ range (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))), ((((if EnvelopingSifted w d1 (WW J w * (s : ℤ) + b) then (1 : ℝ) else 0)) : ℂ) * eC ((a : ℝ) * (s : ℝ) / (q : ℝ))) * (((if EnvelopingSifted w d2 (WW J w * (s : ℤ) + b) then (1 : ℝ) else 0)) : ℂ)))
        = ∑ d1 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors, ∑ d2 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors,
            ((∑ x ∈ range q, (((if EnvelopingSifted w q (WW J w * (x : ℤ) + b) then (1 : ℝ) else 0)) : ℂ) * eC ((a : ℝ) * (x : ℝ) / (q : ℝ))) * ((((envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))) / q : ℕ)) : ℂ)) *
              (((envelopingG w 1 ((M : ℝ) ^ ((1 : ℝ) / 10)) * (if q ∣ Nat.lcm d1 d2 then
                envelopingRho w d1 ((M : ℝ) ^ ((1 : ℝ) / 10)) * envelopingRho w d2 ((M : ℝ) ^ ((1 : ℝ) / 10)) * envelopingDensity w (Nat.lcm d1 d2 / q) else 0)) : ℝ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro d1 hd1
      apply Finset.sum_congr rfl
      intro d2 hd2
      rw [hstep d1 hd1 d2 hd2]
      exact hpair d1 hd1 d2 hd2
    have hfac2 : (∑ d1 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors, ∑ d2 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors, ((∑ x ∈ range q, (((if EnvelopingSifted w q (WW J w * (x : ℤ) + b) then (1 : ℝ) else 0)) : ℂ) * eC ((a : ℝ) * (x : ℝ) / (q : ℝ))) * ((((envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))) / q : ℕ)) : ℂ)) *
        (((envelopingG w 1 ((M : ℝ) ^ ((1 : ℝ) / 10)) * (if q ∣ Nat.lcm d1 d2 then
          envelopingRho w d1 ((M : ℝ) ^ ((1 : ℝ) / 10)) * envelopingRho w d2 ((M : ℝ) ^ ((1 : ℝ) / 10)) * envelopingDensity w (Nat.lcm d1 d2 / q) else 0)) : ℝ) : ℂ))
        = ((∑ x ∈ range q, (((if EnvelopingSifted w q (WW J w * (x : ℤ) + b) then (1 : ℝ) else 0)) : ℂ) * eC ((a : ℝ) * (x : ℝ) / (q : ℝ))) * ((((envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))) / q : ℕ)) : ℂ)) *
          (∑ d1 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors, ∑ d2 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors,
            (((envelopingG w 1 ((M : ℝ) ^ ((1 : ℝ) / 10)) * (if q ∣ Nat.lcm d1 d2 then
              envelopingRho w d1 ((M : ℝ) ^ ((1 : ℝ) / 10)) * envelopingRho w d2 ((M : ℝ) ^ ((1 : ℝ) / 10)) * envelopingDensity w (Nat.lcm d1 d2 / q) else 0)) : ℝ) : ℂ)) := by
      simp only [Finset.mul_sum]
    rw [h1, hfac2, ← hSs]
  have hPq : (1 / (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10)) : ℂ)) * (((envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))) / q : ℕ) : ℂ) = 1 / (q : ℂ) := by
    have hPc : (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10)) : ℂ) ≠ 0 := by exact_mod_cast hP0
    have hPeq : (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10)) : ℂ) = (((envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))) / q : ℕ) : ℂ) * (q : ℂ) := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel hqP]
    have hPq0 : (((envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))) / q : ℕ) : ℂ) ≠ 0 := by
      intro hzero
      rw [hzero, zero_mul] at hPeq
      exact hPc hPeq
    rw [hPeq]
    field_simp
  have hV : envelopingVraw w (WW J w) b M q a
      = (∑ x ∈ range q, (((if EnvelopingSifted w q (WW J w * (x : ℤ) + b) then (1 : ℝ) else 0)) : ℂ) * eC ((a : ℝ) * (x : ℝ) / (q : ℝ))) * (1 / (q : ℂ)) * ((envelopingG w 1 ((M : ℝ) ^ ((1 : ℝ) / 10)) : ℂ) * (((∑ d1 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors, ∑ d2 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors,
        if q ∣ Nat.lcm d1 d2 then envelopingRho w d1 ((M : ℝ) ^ ((1 : ℝ) / 10)) * envelopingRho w d2 ((M : ℝ) ^ ((1 : ℝ) / 10)) *
          envelopingDensity w (Nat.lcm d1 d2 / q) else 0) : ℝ) : ℂ)) := by
    unfold envelopingVraw
    rw [hcore, hinner]
    have hre : (1 / (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10)) : ℂ)) * (((∑ x ∈ range q, (((if EnvelopingSifted w q (WW J w * (x : ℤ) + b) then (1 : ℝ) else 0)) : ℂ) * eC ((a : ℝ) * (x : ℝ) / (q : ℝ))) * ((((envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))) / q : ℕ)) : ℂ)) *
          ((envelopingG w 1 ((M : ℝ) ^ ((1 : ℝ) / 10)) : ℂ) * (((∑ d1 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors, ∑ d2 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors,
        if q ∣ Nat.lcm d1 d2 then envelopingRho w d1 ((M : ℝ) ^ ((1 : ℝ) / 10)) * envelopingRho w d2 ((M : ℝ) ^ ((1 : ℝ) / 10)) *
          envelopingDensity w (Nat.lcm d1 d2 / q) else 0) : ℝ) : ℂ)))
        = (∑ x ∈ range q, (((if EnvelopingSifted w q (WW J w * (x : ℤ) + b) then (1 : ℝ) else 0)) : ℂ) * eC ((a : ℝ) * (x : ℝ) / (q : ℝ))) * ((1 / (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10)) : ℂ)) * ((((envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))) / q : ℕ)) : ℂ)) *
          ((envelopingG w 1 ((M : ℝ) ^ ((1 : ℝ) / 10)) : ℂ) * (((∑ d1 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors, ∑ d2 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors,
        if q ∣ Nat.lcm d1 d2 then envelopingRho w d1 ((M : ℝ) ^ ((1 : ℝ) / 10)) * envelopingRho w d2 ((M : ℝ) ^ ((1 : ℝ) / 10)) *
          envelopingDensity w (Nat.lcm d1 d2 / q) else 0) : ℝ) : ℂ)) := by ring
    rw [hre, hPq]
  rw [hV, norm_mul, norm_mul]
  have hqinv : ‖(1 / (q : ℂ))‖ = 1 / (q : ℝ) := by
    rw [norm_div, norm_one, Complex.norm_natCast]
  have hGS : ‖(envelopingG w 1 ((M : ℝ) ^ ((1 : ℝ) / 10)) : ℂ) * (((∑ d1 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors, ∑ d2 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors,
        if q ∣ Nat.lcm d1 d2 then envelopingRho w d1 ((M : ℝ) ^ ((1 : ℝ) / 10)) * envelopingRho w d2 ((M : ℝ) ^ ((1 : ℝ) / 10)) *
          envelopingDensity w (Nat.lcm d1 d2 / q) else 0) : ℝ) : ℂ)‖ = |envelopingG w 1 ((M : ℝ) ^ ((1 : ℝ) / 10)) * (∑ d1 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors, ∑ d2 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors,
        if q ∣ Nat.lcm d1 d2 then envelopingRho w d1 ((M : ℝ) ^ ((1 : ℝ) / 10)) * envelopingRho w d2 ((M : ℝ) ^ ((1 : ℝ) / 10)) *
          envelopingDensity w (Nat.lcm d1 d2 / q) else 0)| := by
    rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [hqinv, hGS]
  have hcle : ‖(∑ x ∈ range q, (((if EnvelopingSifted w q (WW J w * (x : ℤ) + b) then (1 : ℝ) else 0)) : ℂ) * eC ((a : ℝ) * (x : ℝ) / (q : ℝ)))‖ ≤ (q : ℝ) * envelopingDensity w q := by
    refine (norm_sum_le (s := range q) _).trans ?_
    have hsum : (∑ x ∈ range q, ‖((((if EnvelopingSifted w q (WW J w * (x : ℤ) + b) then (1 : ℝ) else 0)) : ℂ)) * eC ((a : ℝ) * (x : ℝ) / (q : ℝ))‖)
        = ∑ x ∈ range q, (((if EnvelopingSifted w q (WW J w * (x : ℤ) + b) then (1 : ℝ) else 0))) := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : EnvelopingSifted w q (WW J w * (x : ℤ) + b)
      · simp [hx, efsv_eC_norm]
      · simp [hx]
    rw [hsum, efs_count_period (J := J) hw b ((M : ℝ) ^ ((1 : ℝ) / 10)) hqP]
  calc ‖(∑ x ∈ range q, (((if EnvelopingSifted w q (WW J w * (x : ℤ) + b) then (1 : ℝ) else 0)) : ℂ) * eC ((a : ℝ) * (x : ℝ) / (q : ℝ)))‖ * (1 / (q : ℝ)) * |envelopingG w 1 ((M : ℝ) ^ ((1 : ℝ) / 10)) * (∑ d1 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors, ∑ d2 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors,
        if q ∣ Nat.lcm d1 d2 then envelopingRho w d1 ((M : ℝ) ^ ((1 : ℝ) / 10)) * envelopingRho w d2 ((M : ℝ) ^ ((1 : ℝ) / 10)) *
          envelopingDensity w (Nat.lcm d1 d2 / q) else 0)|
      ≤ ((q : ℝ) * envelopingDensity w q) * (1 / (q : ℝ)) * |envelopingG w 1 ((M : ℝ) ^ ((1 : ℝ) / 10)) * (∑ d1 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors, ∑ d2 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors,
        if q ∣ Nat.lcm d1 d2 then envelopingRho w d1 ((M : ℝ) ^ ((1 : ℝ) / 10)) * envelopingRho w d2 ((M : ℝ) ^ ((1 : ℝ) / 10)) *
          envelopingDensity w (Nat.lcm d1 d2 / q) else 0)| := by
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcle (by positivity))
        exact abs_nonneg _
    _ = envelopingDensity w q * |envelopingG w 1 ((M : ℝ) ^ ((1 : ℝ) / 10)) * (∑ d1 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors, ∑ d2 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors,
        if q ∣ Nat.lcm d1 d2 then envelopingRho w d1 ((M : ℝ) ^ ((1 : ℝ) / 10)) * envelopingRho w d2 ((M : ℝ) ^ ((1 : ℝ) / 10)) *
          envelopingDensity w (Nat.lcm d1 d2 / q) else 0)| := by
        have hqr : (q : ℝ) ≠ 0 := by positivity
        field_simp



/-- LEAF: Proposition 4.1 v, page 16, the bound on w_q sharp in display 4.5, class HARD.
Cited: Ramare and Ruzsa reference 18 formulas 4.1.14 and 4.1.15, with formula 4.1.18 for
the sets K_d of display 4.2. The Selberg quadratic form twisted at q, G 1 of z times the sum
of rho_d1 rho_d2 g of lcm d1 d2 over q over q dividing lcm d1 d2, equals G 1 of z times
w_q sharp times the product of p over p minus omega of p over p dividing q, and is at most
an absolute constant to the number of prime factors of q, uniformly in w and z. Exact
rational checks at w equal 5, 6, 10 and z up to 80 give the constant below 1.3. -/
theorem vdecay_quadratic_bound :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ w : ℕ, wBig ≤ w → ∀ z : ℝ, 1 ≤ z → ∀ q : ℕ,
      q ∣ envelopingPrimeProduct w z →
        |envelopingG w 1 z *
          ∑ d1 ∈ (envelopingPrimeProduct w z).divisors,
            ∑ d2 ∈ (envelopingPrimeProduct w z).divisors,
              if q ∣ Nat.lcm d1 d2 then
                envelopingRho w d1 z * envelopingRho w d2 z *
                  envelopingDensity w (Nat.lcm d1 d2 / q)
              else 0| ≤ K ^ q.primeFactors.card := by
  sorry

/-- Page 16, the local density at a square free q is at most 2 to the number of prime
factors of q over q, since omega of p is at most 2. -/
theorem vdecay_density_le (w : ℕ) {q : ℕ} (hq : Squarefree q) :
    envelopingDensity w q ≤ (2 : ℝ) ^ q.primeFactors.card / q := by
  unfold envelopingDensity
  have h1 : ∏ p ∈ q.primeFactors, (envelopingOmega w p : ℝ) / p ≤
      ∏ p ∈ q.primeFactors, (2 : ℝ) / p := by
    apply prod_le_prod₀
    · intro p _; positivity
    · intro p _
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      unfold envelopingOmega
      split_ifs <;> norm_num
  refine h1.trans (le_of_eq ?_)
  rw [prod_div_distrib, prod_const]
  congr 1
  rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hq]

/-- The divisor type bound: K to the number of prime factors of q is at most a constant
depending on K and epsilon times q to the epsilon. Primes p at least K to the 1 over epsilon
have p to the epsilon at least K, and there are at most K to the 1 over epsilon others. -/
theorem vdecay_omega_pow_le {K : ℝ} (hK : 1 ≤ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 1 ≤ q →
      K ^ q.primeFactors.card ≤ C * (q : ℝ) ^ ε := by
  set X := K ^ (1 / ε) with hX
  set T := ⌈X⌉₊ with hT
  refine ⟨K ^ T, by positivity, ?_⟩
  intro q hq
  set S := q.primeFactors.filter (fun p : ℕ => (p : ℝ) < X) with hS
  set L := q.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) < X) with hL
  have hcard : q.primeFactors.card = S.card + L.card :=
    (card_filter_add_card_filter_not _).symm
  have hSc : S.card ≤ T := by
    calc S.card ≤ (range T).card := by
          apply card_le_card
          intro p hp
          rw [mem_filter] at hp
          rw [mem_range]
          have : (p : ℝ) < T := lt_of_lt_of_le hp.2 (Nat.le_ceil X)
          exact_mod_cast this
      _ = T := card_range T
  have hS' : K ^ S.card ≤ K ^ T := pow_le_pow_right₀ hK hSc
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hKX : X ^ ε = K := by
    rw [hX, ← Real.rpow_mul (by linarith), one_div, inv_mul_cancel₀ hε.ne', Real.rpow_one]
  have hL' : K ^ L.card ≤ (q : ℝ) ^ ε := by
    calc K ^ L.card = ∏ p ∈ L, K := by rw [prod_const]
      _ ≤ ∏ p ∈ L, (p : ℝ) ^ ε := by
          apply prod_le_prod₀
          · intro p _; linarith
          · intro p hp
            rw [mem_filter] at hp
            rw [← hKX]
            exact Real.rpow_le_rpow hX0 (not_lt.mp hp.2) hε.le
      _ = (∏ p ∈ L, (p : ℝ)) ^ ε := by
          rw [Real.finsetProd_rpow]
          intro p _; positivity
      _ ≤ (q : ℝ) ^ ε := by
          apply Real.rpow_le_rpow (by positivity) _ hε.le
          have hdvd : ∏ p ∈ L, p ∣ q :=
            dvd_trans (prod_dvd_prod_of_subset _ _ _ (filter_subset _ _))
              (Nat.prod_primeFactors_dvd q)
          have := Nat.le_of_dvd (by omega) hdvd
          rw [← Nat.cast_prod]
          exact_mod_cast this
  rw [hcard, pow_add]
  exact mul_le_mul hS' hL' (by positivity) (by positivity)

/-- Assembly: the exact statement of `enveloping_v_decay` from the two leaves above and
the proved density and divisor type bounds. -/
theorem enveloping_v_decay_of_leaves :
    ∃ D : ℝ → ℝ, (∀ ε : ℝ, 0 < ε → 0 < D ε) ∧
      ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ,
        0 ≤ b → b < WW J w → Amenable (WW J w) b → ∀ M : ℕ, 1 ≤ M →
          ∀ ε : ℝ, 0 < ε → ∀ q : ℕ, 1 ≤ q → ∀ a < q, Nat.Coprime a q →
            ‖envelopingV w (WW J w) b M q a‖ ≤ D ε * (q : ℝ) ^ (ε - 1) := by
  obtain ⟨K, hK1, HB⟩ := vdecay_quadratic_bound
  have hK2 : (1 : ℝ) ≤ 2 * K := by linarith
  choose C hC0 hC using fun (ε : ℝ) (hε : 0 < ε) => vdecay_omega_pow_le hK2 hε
  refine ⟨fun ε => if h : 0 < ε then C ε h else 1, ?_, ?_⟩
  · intro ε hε
    simp only [hε, dite_true]
    exact hC0 ε hε
  intro J w hJ hw b hb hbW hamen M hM ε hε q hq a ha hcop
  simp only [hε, dite_true]
  have hwBig : (5 : ℝ) ≤ wBig := by
    calc (5 : ℝ) ≤ 10 := by norm_num
      _ = (10 : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ wBig := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (Real.one_le_rpow (by norm_num) (by positivity))
  have hw5 : 5 ≤ w := by exact_mod_cast (hwBig.trans hw)
  have hz : (1 : ℝ) ≤ (M : ℝ) ^ ((1 : ℝ) / 10) :=
    Real.one_le_rpow (by exact_mod_cast hM) (by norm_num)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  unfold envelopingV
  split_ifs with hs
  · obtain ⟨hqP, hsq, -, -, -⟩ := hs
    have hA := vdecay_local_eval (J := J) hw5 b M hqP ha hcop
    have hBq := HB w hw _ hz q hqP
    have hD := vdecay_density_le w hsq
    have hc := hC ε hε q hq
    calc _ ≤ _ := hA
      _ ≤ (2 : ℝ) ^ q.primeFactors.card / q * K ^ q.primeFactors.card :=
          mul_le_mul hD hBq (abs_nonneg _) (by positivity)
      _ = (2 * K) ^ q.primeFactors.card / q := by rw [mul_pow]; ring
      _ ≤ C ε hε * (q : ℝ) ^ ε / q := div_le_div_of_nonneg_right hc hq0.le
      _ = C ε hε * (q : ℝ) ^ (ε - 1) := by
          rw [Real.rpow_sub_one hq0.ne', mul_div_assoc]
  · rw [norm_zero]
    exact mul_nonneg (hC0 ε hε).le (Real.rpow_nonneg hq0.le _)

/-- Twin check: the assembly has exactly the type of the original leaf. -/
theorem enveloping_v_decay_twin : type_of% @LeanLab.Teravainen2016.enveloping_v_decay :=
  enveloping_v_decay_of_leaves

end LeanLab.Teravainen2016
