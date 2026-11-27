/-
P0076, Section 4, Proposition 4.1 v, page 16 after display 4.5.
Split of the HARD leaf `enveloping_v_decay` of EnvelopingFourierSplit.lean into an exact
local evaluation bound, the Ramare and Ruzsa bound for the Selberg quadratic form twisted
at q, and a proved divisor type bound K to the omega of q at most C of epsilon times q to
the epsilon. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.EnvelopingFourierSplit
import LeanLab.Teravainen2016.SelbergIdentity

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



/-- Products of local sums over a prime set equal the double subset sum. -/
private theorem vdc_pair_prod (s : Finset ℕ) (φ : ℕ → Bool → Bool → ℝ) :
    ∏ p ∈ s, (φ p true true + φ p true false + φ p false true + φ p false false) =
      ∑ t1 ∈ s.powerset, ∑ t2 ∈ s.powerset, ∏ p ∈ s, φ p (p ∈ t1) (p ∈ t2) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    have hne : ∀ p ∈ s, p ≠ a := fun p hp h => ha (h ▸ hp)
    have hs1 : ∀ (u w : Finset ℕ),
        ∏ p ∈ s, φ p (p ∈ u) (p ∈ insert a w) = ∏ p ∈ s, φ p (p ∈ u) (p ∈ w) := by
      intro u w
      exact Finset.prod_congr rfl
        (fun p hp => by simp [Finset.mem_insert, hne p hp])
    have hs2 : ∀ (u w : Finset ℕ),
        ∏ p ∈ s, φ p (p ∈ insert a u) (p ∈ w) = ∏ p ∈ s, φ p (p ∈ u) (p ∈ w) := by
      intro u w
      exact Finset.prod_congr rfl
        (fun p hp => by simp [Finset.mem_insert, hne p hp])
    have hs12 : ∀ (u w : Finset ℕ),
        ∏ p ∈ s, φ p (p ∈ insert a u) (p ∈ insert a w) = ∏ p ∈ s, φ p (p ∈ u) (p ∈ w) := by
      intro u w
      exact Finset.prod_congr rfl
        (fun p hp => by simp [Finset.mem_insert, hne p hp])
    -- values at the inserted prime
    have hff : ∀ (u : Finset ℕ), a ∉ u → φ a (a ∈ u) (a ∈ u) = φ a false false := by
      intro u hu
      congr 1 <;> simp [hu]
    have inner : ∀ (w1 : Finset ℕ), w1 ⊆ s →
        (∑ t2 ∈ (insert a s).powerset, ∏ p ∈ insert a s, φ p (p ∈ w1) (p ∈ t2))
        = (∑ t2 ∈ s.powerset, ∏ p ∈ s, φ p (p ∈ w1) (p ∈ t2)) * φ a (a ∈ w1) (a ∈ w1)
          + (∑ t2 ∈ s.powerset, ∏ p ∈ s, φ p (p ∈ w1) (p ∈ t2)) * φ a (a ∈ w1) true := by
      intro w1 hw1
      have hna : ¬ (a ∈ w1) := fun h => ha (hw1 h)
      rw [Finset.sum_powerset_insert ha, Finset.sum_mul, Finset.sum_mul]
      congr 1
      · apply Finset.sum_congr rfl
        intro u2 hu2
        have hu2s : u2 ⊆ s := Finset.mem_powerset.mp hu2
        have hnu2 : ¬ (a ∈ u2) := fun h => ha (hu2s h)
        have hv : φ a (a ∈ w1) (a ∈ u2) = φ a (a ∈ w1) (a ∈ w1) := by
          congr 1 <;> simp [hna, hnu2]
        rw [Finset.prod_insert ha, hv, mul_comm]
      · apply Finset.sum_congr rfl
        intro u2 hu2
        have hv : φ a (a ∈ w1) (a ∈ insert a u2) = φ a (a ∈ w1) true := by simp
        rw [Finset.prod_insert ha, hs1 w1 u2, hv, mul_comm]
    have inner2 : ∀ (w1 : Finset ℕ), w1 ⊆ s →
        (∑ t2 ∈ (insert a s).powerset, ∏ p ∈ insert a s, φ p (p ∈ insert a w1) (p ∈ t2))
        = (∑ t2 ∈ s.powerset, ∏ p ∈ s, φ p (p ∈ w1) (p ∈ t2)) * φ a true false
          + (∑ t2 ∈ s.powerset, ∏ p ∈ s, φ p (p ∈ w1) (p ∈ t2)) * φ a true true := by
      intro w1 hw1
      rw [Finset.sum_powerset_insert ha, Finset.sum_mul, Finset.sum_mul]
      congr 1
      · apply Finset.sum_congr rfl
        intro u2 hu2
        have hu2s : u2 ⊆ s := Finset.mem_powerset.mp hu2
        have hnu2 : ¬ (a ∈ u2) := fun h => ha (hu2s h)
        have hv : φ a (a ∈ insert a w1) (a ∈ u2) = φ a true false := by
          congr 1 <;> simp [hnu2]
        rw [Finset.prod_insert ha, hs2 w1 u2, hv, mul_comm]
      · apply Finset.sum_congr rfl
        intro u2 hu2
        have hv : φ a (a ∈ insert a w1) (a ∈ insert a u2) = φ a true true := by simp
        rw [Finset.prod_insert ha, hs12 w1 u2, hv, mul_comm]
    rw [Finset.prod_insert ha, ih, Finset.sum_powerset_insert ha]
    have S1 : (∑ t ∈ s.powerset, ∑ t2 ∈ (insert a s).powerset,
          ∏ p ∈ insert a s, φ p (p ∈ t) (p ∈ t2))
        = ∑ t ∈ s.powerset, ((∑ t2 ∈ s.powerset, ∏ p ∈ s, φ p (p ∈ t) (p ∈ t2)) * φ a false false
            + (∑ t2 ∈ s.powerset, ∏ p ∈ s, φ p (p ∈ t) (p ∈ t2)) * φ a false true) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [inner t (Finset.mem_powerset.mp ht)]
      have hna : ¬ (a ∈ t) := fun h => ha (Finset.mem_powerset.mp ht h)
      rw [show φ a (a ∈ t) (a ∈ t) = φ a false false from by congr 1 <;> simp [hna],
        show φ a (a ∈ t) true = φ a false true from by congr 1 <;> simp [hna]]
    have S2 : (∑ t ∈ s.powerset, ∑ t2 ∈ (insert a s).powerset,
          ∏ p ∈ insert a s, φ p (p ∈ insert a t) (p ∈ t2))
        = ∑ t ∈ s.powerset, ((∑ t2 ∈ s.powerset, ∏ p ∈ s, φ p (p ∈ t) (p ∈ t2)) * φ a true false
            + (∑ t2 ∈ s.powerset, ∏ p ∈ s, φ p (p ∈ t) (p ∈ t2)) * φ a true true) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [inner2 t (Finset.mem_powerset.mp ht)]
    rw [S1, S2, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
    ring

/-- Splitting a sum over subsets into a free part and a fixed part. -/
private theorem vdc_sum_powerset_split {s off qs : Finset ℕ} (hu : off ∪ qs = s)
    (hd : Disjoint off qs) (G : Finset ℕ → ℝ) :
    ∑ t ∈ s.powerset, G t = ∑ n ∈ off.powerset, ∑ a ∈ qs.powerset, G (n ∪ a) := by
  have hprod : (∑ n ∈ off.powerset, ∑ a ∈ qs.powerset, G (n ∪ a))
      = ∑ x ∈ off.powerset ×ˢ qs.powerset, G (x.1 ∪ x.2) :=
    (Finset.sum_product _ _ (fun x : Finset ℕ × Finset ℕ => G (x.1 ∪ x.2))).symm
  rw [hprod]
  refine (Finset.sum_bij (fun (x : Finset ℕ × Finset ℕ) _ => x.1 ∪ x.2) ?_ ?_ ?_ ?_).symm
  · rintro ⟨n, a⟩ hx
    simp only [Finset.mem_product, Finset.mem_powerset] at hx
    refine Finset.mem_powerset.mpr ?_
    rw [← hu]
    exact Finset.union_subset_union hx.1 hx.2
  · rintro ⟨n1, a1⟩ hx1 ⟨n2, a2⟩ hx2 heq
    simp only [Finset.mem_product, Finset.mem_powerset] at hx1 hx2
    obtain ⟨hn1, ha1⟩ := hx1
    obtain ⟨hn2, ha2⟩ := hx2
    have hdj : ∀ x, x ∈ off → x ∉ qs := fun x hx hx' => Finset.disjoint_left.mp hd hx hx'
    have heq' : n1 ∪ a1 = n2 ∪ a2 := heq
    have hnn : n1 = n2 := by
      refine Finset.ext (fun x => ?_)
      constructor
      · intro hx
        have h1 : x ∈ n1 ∪ a1 := Finset.mem_union_left _ hx
        rw [heq'] at h1
        rcases Finset.mem_union.mp h1 with h | h
        · exact h
        · exact absurd (ha2 h) (hdj x (hn1 hx))
      · intro hx
        have h1 : x ∈ n2 ∪ a2 := Finset.mem_union_left _ hx
        rw [← heq'] at h1
        rcases Finset.mem_union.mp h1 with h | h
        · exact h
        · exact absurd (ha1 h) (hdj x (hn2 hx))
    have haa : a1 = a2 := by
      refine Finset.ext (fun x => ?_)
      constructor
      · intro hx
        have h1 : x ∈ n1 ∪ a1 := Finset.mem_union_right _ hx
        rw [heq'] at h1
        rcases Finset.mem_union.mp h1 with h | h
        · exact absurd (ha1 hx) (hdj x (hn2 h))
        · exact h
      · intro hx
        have h1 : x ∈ n2 ∪ a2 := Finset.mem_union_right _ hx
        rw [← heq'] at h1
        rcases Finset.mem_union.mp h1 with h | h
        · exact absurd (ha2 hx) (hdj x (hn1 h))
        · exact h
    rw [hnn, haa]
  · intro t ht
    refine ⟨(t ∩ off, t ∩ qs), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_powerset]
      exact ⟨Finset.inter_subset_right, Finset.inter_subset_right⟩
    · refine Finset.ext (fun x => ?_)
      simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
      · intro h
        have ht' : t ⊆ off ∪ qs := by rw [hu]; exact Finset.mem_powerset.mp ht
        rcases Finset.mem_union.mp (ht' h) with h' | h'
        · exact Or.inl ⟨h, h'⟩
        · exact Or.inr ⟨h, h'⟩
  · rintro ⟨n, a⟩ hx
    rfl


/-- `P` is squarefree. -/
private theorem vdc_P_sqfree {w : ℕ} (hw : 5 ≤ w) (z : ℝ) :
    Squarefree (envelopingPrimeProduct w z) :=
  (enveloping_divisor_support (J := 5) hw (dvd_refl _)).1

/-- Every element of the prime support of `P` is prime. -/
private theorem vdc_prime {w : ℕ} {z : ℝ} {p : ℕ}
    (hp : p ∈ (envelopingPrimeProduct w z).primeFactors) : p.Prime :=
  Nat.prime_of_mem_primeFactors hp

/-- The divisor `E t`. -/
private theorem vdc_E_ne (t : Finset ℕ) (hp : ∀ p ∈ t, p.Prime) :
    ∏ p ∈ t, p ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun p hp' => (hp p hp').ne_zero)

private theorem vdc_E_sqfree (t : Finset ℕ) (hp : ∀ p ∈ t, p.Prime) :
    Squarefree (∏ p ∈ t, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i hi j hj hij
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hp i hi) (hp j hj)).mpr hij)
  · intro i hi
    exact (hp i hi).squarefree

private theorem vdc_E_pf (t : Finset ℕ) (hp : ∀ p ∈ t, p.Prime) :
    (∏ p ∈ t, p).primeFactors = t :=
  Nat.primeFactors_prod hp

private theorem vdc_E_dvd {w : ℕ} (hw : 5 ≤ w) {z : ℝ} {t : Finset ℕ}
    (ht : t ⊆ (envelopingPrimeProduct w z).primeFactors) :
    ∏ p ∈ t, p ∣ envelopingPrimeProduct w z := by
  calc ∏ p ∈ t, p ∣ ∏ p ∈ (envelopingPrimeProduct w z).primeFactors, p :=
        prod_dvd_prod_of_subset _ _ _ ht
    _ = envelopingPrimeProduct w z := Nat.prod_primeFactors_of_squarefree (vdc_P_sqfree hw z)

/-- `H` at `E t` is the product of the local factors. -/
private theorem vdc_H_E {w : ℕ} (hw : 5 ≤ w) {z : ℝ} {t : Finset ℕ}
    (ht : t ⊆ (envelopingPrimeProduct w z).primeFactors) :
    envelopingH w (∏ p ∈ t, p) =
      ∏ p ∈ t, (envelopingOmega w p : ℝ) / (p - envelopingOmega w p : ℕ) :=
  sel_h_prod w (vdc_P_sqfree hw z) ht

/-- `g` at `E t` is the product of the local densities. -/
private theorem vdc_g_E {w : ℕ} {t : Finset ℕ} (hp : ∀ p ∈ t, p.Prime) :
    envelopingDensity w (∏ p ∈ t, p) = ∏ p ∈ t, (envelopingOmega w p : ℝ) / p := by
  unfold envelopingDensity
  rw [vdc_E_pf t hp]

private theorem vdc_cardFactors_E (t : Finset ℕ) (hp : ∀ p ∈ t, p.Prime) :
    ArithmeticFunction.cardFactors (∏ p ∈ t, p) = t.card := by
  induction t using Finset.induction with
  | empty => simp [ArithmeticFunction.cardFactors]
  | insert a t ha ih =>
    have hpa : a.Prime := hp a (Finset.mem_insert_self a t)
    have hpt : ∀ p ∈ t, p.Prime := fun p hp' => hp p (Finset.mem_insert_of_mem hp')
    rw [Finset.prod_insert ha,
      ArithmeticFunction.cardFactors_mul hpa.ne_zero (vdc_E_ne t hpt), ih hpt,
      ArithmeticFunction.cardFactors_apply_prime hpa, Finset.card_insert_of_notMem ha]
    omega

/-- Moebius at `E t`. -/
private theorem vdc_mu_E (t : Finset ℕ) (hp : ∀ p ∈ t, p.Prime) :
    (ArithmeticFunction.moebius (∏ p ∈ t, p) : ℝ) = ∏ p ∈ t, (-1 : ℝ) := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree (vdc_E_sqfree t hp),
    vdc_cardFactors_E t hp, Finset.prod_const]
  push_cast
  ring


/-- The twisted kernel at `E t` as a product of local factors over the whole prime support. -/
private theorem vdc_W_E {w q : ℕ} {z : ℝ} {t : Finset ℕ}
    (ht : t ⊆ (envelopingPrimeProduct w z).primeFactors)
    (hq : q ∣ envelopingPrimeProduct w z) :
    (if q ∣ ∏ p ∈ t, p then envelopingDensity w ((∏ p ∈ t, p) / q) else 0)
      = ∏ p ∈ (envelopingPrimeProduct w z).primeFactors,
          (if p ∈ t then (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p)
           else (if p ∣ q then 0 else 1)) := by
  set s := (envelopingPrimeProduct w z).primeFactors with hs
  have hP0 : envelopingPrimeProduct w z ≠ 0 := envelopingPrimeProduct_ne_zero w z
  have hpT : ∀ p ∈ t, p.Prime := fun p hp => vdc_prime (ht hp)
  have hsqP : Squarefree (envelopingPrimeProduct w z) := by
    unfold envelopingPrimeProduct
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i hi j hj hij
      exact Nat.coprime_iff_isRelPrime.mp
        ((Nat.coprime_primes (Finset.mem_filter.mp hi).2.1 (Finset.mem_filter.mp hj).2.1).mpr hij)
    · intro i hi
      exact (Finset.mem_filter.mp hi).2.1.prime.squarefree
  have hpS : ∀ p ∈ s, p.Prime := fun p hp => vdc_prime (hs ▸ hp)
  have hEt0 : ∏ p ∈ t, p ≠ 0 := vdc_E_ne t hpT
  have hEtpf : (∏ p ∈ t, p).primeFactors = t := vdc_E_pf t hpT
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hP0 (Nat.eq_zero_of_zero_dvd hq)
  -- the right hand side, split as (s \ t) and t
  have hsplitR : ∏ p ∈ s, (if p ∈ t then (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p)
        else (if p ∣ q then 0 else 1))
      = (∏ p ∈ s \ t, (if p ∈ t then (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p)
          else (if p ∣ q then 0 else 1)))
        * ∏ p ∈ t, (if p ∈ t then (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p)
          else (if p ∣ q then 0 else 1)) :=
    (Finset.prod_sdiff ht).symm
  by_cases hcase : q ∣ ∏ p ∈ t, p
  · rw [if_pos hcase, hsplitR]
    -- the three ingredients
    have hdq0 : (∏ p ∈ t, p) / q ≠ 0 := by
      intro h
      exact hEt0 (by rw [← Nat.mul_div_cancel' hcase, h, mul_zero])
    have hmul : q * ((∏ p ∈ t, p) / q) = ∏ p ∈ t, p := Nat.mul_div_cancel' hcase
    have hsqdiv : Squarefree ((∏ p ∈ t, p) / q) :=
      (vdc_E_sqfree t hpT).squarefree_of_dvd (Nat.div_dvd_of_dvd hcase)
    have hsqmul : Squarefree (q * ((∏ p ∈ t, p) / q)) := by rw [hmul]; exact vdc_E_sqfree t hpT
    have hcop : Nat.Coprime q ((∏ p ∈ t, p) / q) := Nat.coprime_of_squarefree_mul hsqmul
    have hdisj : Disjoint q.primeFactors ((∏ p ∈ t, p) / q).primeFactors :=
      hcop.disjoint_primeFactors
    have hpf : q.primeFactors ∪ ((∏ p ∈ t, p) / q).primeFactors = t := by
      rw [← Nat.primeFactors_mul hq0 hdq0, hmul, hEtpf]
    have hqsub : q.primeFactors ⊆ t := by rw [← hpf]; exact Finset.subset_union_left
    have hdiff : ((∏ p ∈ t, p) / q).primeFactors = t \ q.primeFactors := by
      conv_rhs => rw [← hpf]
      exact (Finset.union_sdiff_cancel_left hdisj).symm
    have hprq : ∀ p ∈ ((∏ p ∈ t, p) / q).primeFactors, p.Prime := by
      intro p hp
      rw [hdiff] at hp
      exact hpT p (Finset.mem_sdiff.mp hp).1
    have hgdiv : envelopingDensity w ((∏ p ∈ t, p) / q) =
        ∏ p ∈ t \ q.primeFactors, (envelopingOmega w p : ℝ) / p := by
      have h1 : envelopingDensity w ((∏ p ∈ t, p) / q) =
          ∏ p ∈ ((∏ p ∈ t, p) / q).primeFactors, (envelopingOmega w p : ℝ) / p := by
        refine Eq.trans ?_ (vdc_g_E (w := w) hprq)
        exact congrArg (envelopingDensity w) (Nat.prod_primeFactors_of_squarefree hsqdiv).symm
      rw [h1, hdiff]
    have hleft : ∏ p ∈ s \ t, (if p ∈ t then (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p)
        else (if p ∣ q then 0 else 1)) = 1 := by
      apply Finset.prod_eq_one
      intro p hp
      rw [Finset.mem_sdiff] at hp
      have hpt : p ∉ t := hp.2
      have hpq : ¬ (p ∣ q) := by
        intro hd
        exact hpt (hqsub (Nat.mem_primeFactors.mpr ⟨hpS p hp.1, hd, hq0⟩))
      simp [hpt, hpq]
    have hright : ∏ p ∈ t, (if p ∈ t then (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p)
        else (if p ∣ q then 0 else 1))
        = ∏ p ∈ t \ q.primeFactors, (envelopingOmega w p : ℝ) / p := by
      have step1 : ∏ p ∈ t, (if p ∈ t then (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p)
          else (if p ∣ q then 0 else 1))
          = ∏ p ∈ t, (if p ∈ q.primeFactors then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) := by
        apply Finset.prod_congr rfl
        intro p hp
        have hpq : p ∣ q ↔ p ∈ q.primeFactors :=
          ⟨fun hd => Nat.mem_primeFactors.mpr ⟨hpT p hp, hd, hq0⟩, Nat.dvd_of_mem_primeFactors⟩
        by_cases h1 : p ∣ q
        · simp [hp, h1, hpq.mp h1]
        · have h2 : p ∉ q.primeFactors := fun h => h1 (hpq.mpr h)
          simp [hp, h1, h2]
      have step2 : ∏ p ∈ t ∩ q.primeFactors,
          (if p ∈ q.primeFactors then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) = 1 := by
        apply Finset.prod_eq_one
        intro p hp
        rw [Finset.mem_inter] at hp
        simp [hp.2]
      have step3 : t \ (t ∩ q.primeFactors) = t \ q.primeFactors := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_inter]
        tauto
      rw [step1, ← Finset.prod_sdiff (Finset.inter_subset_left (s₁ := t) (s₂ := q.primeFactors)),
        step2, step3, mul_one]
      apply Finset.prod_congr rfl
      intro p hp
      rw [Finset.mem_sdiff] at hp
      simp [hp.2]
    rw [hleft, hright, hgdiv, one_mul]
  · rw [if_neg hcase, hsplitR]
    have hex : ∃ p ∈ q.primeFactors, p ∉ t := by
      by_contra hc
      push_neg at hc
      have hd : q ∣ ∏ p ∈ t, p := by
        have h1 : q = ∏ p ∈ q.primeFactors, p :=
          (Nat.prod_primeFactors_of_squarefree (hsqP.squarefree_of_dvd hq)).symm
        rw [h1]
        exact prod_dvd_prod_of_subset _ _ _ hc
      exact hcase hd
    obtain ⟨p, hp, hpt⟩ := hex
    have hpq : p ∣ q := Nat.dvd_of_mem_primeFactors hp
    have hps : p ∈ s := by
      rw [hs]
      exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp, hpq.trans hq, hP0⟩
    have hzero : (if p ∈ t then (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p)
        else (if p ∣ q then 0 else 1)) = 0 := by
      simp [hpt, hpq]
    have hz1 : ∏ p ∈ s \ t, (if p ∈ t then (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p)
        else (if p ∣ q then 0 else 1)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨hps, hpt⟩) hzero
    rw [hz1, zero_mul]


/-- Merge three products of local factors over the same set. -/
private theorem vdc_merge_products (s u1 u2 : Finset ℕ) (c1 c2 : ℕ → ℝ)
    (k : ℕ → Bool → ℝ) :
    (∏ p ∈ s, (if p ∈ u1 then c1 p else 1)) * (∏ p ∈ s, (if p ∈ u2 then c2 p else 1))
      * (∏ p ∈ s, k p (p ∈ u1 ∨ p ∈ u2))
    = ∏ p ∈ s, ((if p ∈ u1 then c1 p else 1) * (if p ∈ u2 then c2 p else 1)
        * k p (p ∈ u1 ∨ p ∈ u2)) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]

/-- A product over a subset as a product over the ambient set with ones. -/
private theorem vdc_prod_ite_mem_single {s u : Finset ℕ} (hu : u ⊆ s) (c : ℕ → ℝ) :
    (∏ p ∈ u, c p) = ∏ p ∈ s, (if p ∈ u then c p else 1) :=
  ((Finset.prod_ite_mem s u c).trans (by rw [Finset.inter_eq_right.mpr hu])).symm

/-- The least common multiple of two products of distinct primes is the product over the union. -/
private theorem vdc_lcm_E (u1 u2 : Finset ℕ) (h1 : ∀ p ∈ u1, p.Prime)
    (h2 : ∀ p ∈ u2, p.Prime) :
    Nat.lcm (∏ p ∈ u1, p) (∏ p ∈ u2, p) = ∏ p ∈ u1 ∪ u2, p := by
  have hn1 : ∏ p ∈ u1, p ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun p hp => (h1 p hp).ne_zero)
  have hn2 : ∏ p ∈ u2, p ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun p hp => (h2 p hp).ne_zero)
  have hpf : (Nat.lcm (∏ p ∈ u1, p) (∏ p ∈ u2, p)).primeFactors = u1 ∪ u2 := by
    rw [sel_pf_lcm hn1 hn2, vdc_E_pf u1 h1, vdc_E_pf u2 h2]
  refine Nat.dvd_antisymm ?_ ?_
  · exact Nat.lcm_dvd (prod_dvd_prod_of_subset _ _ _ Finset.subset_union_left)
      (prod_dvd_prod_of_subset _ _ _ Finset.subset_union_right)
  · rw [← hpf]
    exact Nat.prod_primeFactors_dvd _

/-- `mu` over `g` at `E u` is the product of the local ratios. -/
private theorem vdc_mu_div_g {w : ℕ} (t : Finset ℕ) (hp : ∀ p ∈ t, p.Prime) :
    (ArithmeticFunction.moebius (∏ p ∈ t, p) : ℝ) / envelopingDensity w (∏ p ∈ t, p)
      = ∏ p ∈ t, (-(1 : ℝ) / ((envelopingOmega w p : ℝ) / p)) := by
  rw [vdc_mu_E t hp, vdc_g_E hp]
  simp only [Finset.prod_div_distrib]

/-- The local density at a prime of the support is positive. -/
private theorem vdc_omega_pos {w : ℕ} {z : ℝ} {p : ℕ}
    (hp : p ∈ (envelopingPrimeProduct w z).primeFactors) :
    (0 : ℝ) < (envelopingOmega w p : ℝ) := by
  have hpp := vdc_prime hp
  have hwp : w < p := efs_prime_gt hpp (Nat.dvd_of_mem_primeFactors hp)
  unfold envelopingOmega
  rw [if_neg (by omega)]
  split_ifs <;> norm_num

/-- Merge three products over the same set. -/
private theorem vdc_merge3 (s : Finset ℕ) (f1 f2 f3 : ℕ → ℝ) :
    (∏ p ∈ s, f1 p) * (∏ p ∈ s, f2 p) * (∏ p ∈ s, f3 p)
      = ∏ p ∈ s, (f1 p * f2 p * f3 p) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]


/-- The twisted summand at `E u1`, `E u2` factorises over the primes of the support. -/
private theorem vdc_weight_factor {w q : ℕ} {z : ℝ} {u1 u2 : Finset ℕ}
    (hu1 : u1 ⊆ (envelopingPrimeProduct w z).primeFactors)
    (hu2 : u2 ⊆ (envelopingPrimeProduct w z).primeFactors)
    (hq : q ∣ envelopingPrimeProduct w z) :
    (if q ∣ Nat.lcm (∏ p ∈ u1, p) (∏ p ∈ u2, p) then
        (ArithmeticFunction.moebius (∏ p ∈ u1, p) : ℝ) *
            (ArithmeticFunction.moebius (∏ p ∈ u2, p) : ℝ) *
          envelopingDensity w (Nat.lcm (∏ p ∈ u1, p) (∏ p ∈ u2, p) / q)
      else 0)
      / (envelopingDensity w (∏ p ∈ u1, p) * envelopingDensity w (∏ p ∈ u2, p))
      = ∏ p ∈ (envelopingPrimeProduct w z).primeFactors,
          ((if p ∈ u1 then -(1 : ℝ) / ((envelopingOmega w p : ℝ) / p) else 1)
            * (if p ∈ u2 then -(1 : ℝ) / ((envelopingOmega w p : ℝ) / p) else 1)
            * (if p ∈ u1 ∨ p ∈ u2 then (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p)
               else (if p ∣ q then 0 else 1))) := by
  have hp1 : ∀ p ∈ u1, p.Prime := fun p hp => vdc_prime (hu1 hp)
  have hp2 : ∀ p ∈ u2, p.Prime := fun p hp => vdc_prime (hu2 hp)
  have hup : u1 ∪ u2 ⊆ (envelopingPrimeProduct w z).primeFactors :=
    Finset.union_subset hu1 hu2
  have hg1 : envelopingDensity w (∏ p ∈ u1, p) ≠ 0 := by
    rw [vdc_g_E hp1]
    refine Finset.prod_ne_zero_iff.mpr (fun p hp => ?_)
    have hpos := vdc_omega_pos (hu1 hp)
    have : (0 : ℝ) < p := by exact_mod_cast (hp1 p hp).pos
    positivity
  have hg2 : envelopingDensity w (∏ p ∈ u2, p) ≠ 0 := by
    rw [vdc_g_E hp2]
    refine Finset.prod_ne_zero_iff.mpr (fun p hp => ?_)
    have hpos := vdc_omega_pos (hu2 hp)
    have : (0 : ℝ) < p := by exact_mod_cast (hp2 p hp).pos
    positivity
  rw [vdc_lcm_E u1 u2 hp1 hp2]
  have hnum : (if q ∣ ∏ p ∈ u1 ∪ u2, p then
        (ArithmeticFunction.moebius (∏ p ∈ u1, p) : ℝ) *
            (ArithmeticFunction.moebius (∏ p ∈ u2, p) : ℝ) *
          envelopingDensity w ((∏ p ∈ u1 ∪ u2, p) / q)
      else 0)
      = (ArithmeticFunction.moebius (∏ p ∈ u1, p) : ℝ) *
          (ArithmeticFunction.moebius (∏ p ∈ u2, p) : ℝ) *
        (if q ∣ ∏ p ∈ u1 ∪ u2, p then
          envelopingDensity w ((∏ p ∈ u1 ∪ u2, p) / q) else 0) := by
    by_cases h : q ∣ ∏ p ∈ u1 ∪ u2, p <;> simp [h]
  rw [hnum, vdc_W_E hup hq]
  have hkey : ((ArithmeticFunction.moebius (∏ p ∈ u1, p) : ℝ) *
        (ArithmeticFunction.moebius (∏ p ∈ u2, p) : ℝ) *
        ∏ p ∈ (envelopingPrimeProduct w z).primeFactors,
          (if p ∈ u1 ∪ u2 then (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p)
           else (if p ∣ q then 0 else 1)))
      / (envelopingDensity w (∏ p ∈ u1, p) * envelopingDensity w (∏ p ∈ u2, p))
      = ((ArithmeticFunction.moebius (∏ p ∈ u1, p) : ℝ) / envelopingDensity w (∏ p ∈ u1, p)) *
          ((ArithmeticFunction.moebius (∏ p ∈ u2, p) : ℝ) / envelopingDensity w (∏ p ∈ u2, p)) *
        ∏ p ∈ (envelopingPrimeProduct w z).primeFactors,
          (if p ∈ u1 ∪ u2 then (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p)
           else (if p ∣ q then 0 else 1)) := by
    rw [div_eq_iff (mul_ne_zero hg1 hg2)]
    field_simp
  rw [hkey]
  rw [vdc_mu_div_g u1 hp1]
  rw [vdc_mu_div_g u2 hp2]
  rw [vdc_prod_ite_mem_single hu1]
  rw [vdc_prod_ite_mem_single hu2]
  simp only [Finset.mem_union]
  rw [vdc_merge3]


/-- Pointwise expansion of one summand of the twisted Selberg form. -/
private theorem vdc_expand {w q : ℕ} (hw : 5 ≤ w) {z : ℝ} (hz : 1 ≤ z) {d1 d2 : ℕ}
    (hd1 : d1 ∈ (envelopingPrimeProduct w z).divisors)
    (hd2 : d2 ∈ (envelopingPrimeProduct w z).divisors) :
    (if q ∣ Nat.lcm d1 d2 then
        (ArithmeticFunction.moebius d1 : ℝ) * envelopingG w d1 z *
          ((ArithmeticFunction.moebius d2 : ℝ) * envelopingG w d2 z) *
          envelopingDensity w (Nat.lcm d1 d2 / q)
      else 0)
    = ∑ e1 ∈ (envelopingPrimeProduct w z).divisors,
        ∑ e2 ∈ (envelopingPrimeProduct w z).divisors,
        (if d1 ∣ e1 then (if (e1 : ℝ) ≤ z then envelopingH w e1 else 0) else 0) *
        (if d2 ∣ e2 then (if (e2 : ℝ) ≤ z then envelopingH w e2 else 0) else 0) *
        ((if q ∣ Nat.lcm d1 d2 then
            (ArithmeticFunction.moebius d1 : ℝ) * (ArithmeticFunction.moebius d2 : ℝ) *
              envelopingDensity w (Nat.lcm d1 d2 / q) else 0) /
          (envelopingDensity w d1 * envelopingDensity w d2)) := by
  have hgs1 : envelopingDensity w d1 ≠ 0 := sel_g_ne w z (Nat.dvd_of_mem_divisors hd1)
  have hgs2 : envelopingDensity w d2 ≠ 0 := sel_g_ne w z (Nat.dvd_of_mem_divisors hd2)
  set c : ℝ := ((if q ∣ Nat.lcm d1 d2 then
      (ArithmeticFunction.moebius d1 : ℝ) * (ArithmeticFunction.moebius d2 : ℝ) *
        envelopingDensity w (Nat.lcm d1 d2 / q) else 0) /
    (envelopingDensity w d1 * envelopingDensity w d2)) with hc
  set S1 : ℝ := ∑ e ∈ (envelopingPrimeProduct w z).divisors,
    (if d1 ∣ e then (if (e : ℝ) ≤ z then envelopingH w e else 0) else 0) with hS1
  set S2 : ℝ := ∑ e ∈ (envelopingPrimeProduct w z).divisors,
    (if d2 ∣ e then (if (e : ℝ) ≤ z then envelopingH w e else 0) else 0) with hS2
  have key : ∀ d : ℕ, d ∈ (envelopingPrimeProduct w z).divisors →
      envelopingG w d z =
        (∑ e ∈ (envelopingPrimeProduct w z).divisors,
          (if d ∣ e then (if (e : ℝ) ≤ z then envelopingH w e else 0) else 0)) /
          envelopingDensity w d := by
    intro d hd
    rw [eq_div_iff (sel_g_ne w z (Nat.dvd_of_mem_divisors hd)), mul_comm]
    refine (sel_gG w hw z hz hd).trans ?_
    apply Finset.sum_congr rfl
    intro e he
    by_cases h : d ∣ e <;> by_cases h2 : (e : ℝ) ≤ z <;> simp [h, h2]
  rw [key d1 hd1, key d2 hd2]
  -- the right hand side collapses to `S1 * S2 * c`
  have hA : ∀ e1 ∈ (envelopingPrimeProduct w z).divisors,
      (∑ e2 ∈ (envelopingPrimeProduct w z).divisors,
        (if d1 ∣ e1 then (if (e1 : ℝ) ≤ z then envelopingH w e1 else 0) else 0) *
        (if d2 ∣ e2 then (if (e2 : ℝ) ≤ z then envelopingH w e2 else 0) else 0) * c)
      = (if d1 ∣ e1 then (if (e1 : ℝ) ≤ z then envelopingH w e1 else 0) else 0) *
        ((∑ e2 ∈ (envelopingPrimeProduct w z).divisors,
          (if d2 ∣ e2 then (if (e2 : ℝ) ≤ z then envelopingH w e2 else 0) else 0)) * c) := by
    intro e1 he1
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e2 he2
    ring
  have hstep1 : (∑ e1 ∈ (envelopingPrimeProduct w z).divisors,
        ∑ e2 ∈ (envelopingPrimeProduct w z).divisors,
        (if d1 ∣ e1 then (if (e1 : ℝ) ≤ z then envelopingH w e1 else 0) else 0) *
        (if d2 ∣ e2 then (if (e2 : ℝ) ≤ z then envelopingH w e2 else 0) else 0) * c)
      = (∑ e1 ∈ (envelopingPrimeProduct w z).divisors,
          (if d1 ∣ e1 then (if (e1 : ℝ) ≤ z then envelopingH w e1 else 0) else 0)) *
        (∑ e2 ∈ (envelopingPrimeProduct w z).divisors,
          (if d2 ∣ e2 then (if (e2 : ℝ) ≤ z then envelopingH w e2 else 0) else 0) * c) := by
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro e1 _
    apply Finset.sum_congr rfl
    intro e2 _
    ring
  have hstep2 : (∑ e2 ∈ (envelopingPrimeProduct w z).divisors,
        (if d2 ∣ e2 then (if (e2 : ℝ) ≤ z then envelopingH w e2 else 0) else 0) * c)
      = (∑ e2 ∈ (envelopingPrimeProduct w z).divisors,
        (if d2 ∣ e2 then (if (e2 : ℝ) ≤ z then envelopingH w e2 else 0) else 0)) * c :=
    (Finset.sum_mul _ _ _).symm
  rw [hstep1, hstep2, ← hS1, ← hS2]
  by_cases hC : q ∣ Nat.lcm d1 d2
  · rw [if_pos hC, hc]
    simp only [hC, if_pos]
    field_simp
    try ring
  · rw [if_neg hC, hc]
    simp only [hC, if_neg, not_false_eq_true, zero_div, mul_zero, and_self, and_true]


/-- Global assembly: the twisted Selberg form as a sum over the full range with a filtered
inner sum. -/
private theorem vdc_assemble {w q : ℕ} (hw : 5 ≤ w) {z : ℝ} (hz : 1 ≤ z)
    (hq : q ∣ envelopingPrimeProduct w z) :
    (∑ d1 ∈ (envelopingPrimeProduct w z).divisors,
      ∑ d2 ∈ (envelopingPrimeProduct w z).divisors,
        (if q ∣ Nat.lcm d1 d2 then
          (ArithmeticFunction.moebius d1 : ℝ) * envelopingG w d1 z *
            ((ArithmeticFunction.moebius d2 : ℝ) * envelopingG w d2 z) *
            envelopingDensity w (Nat.lcm d1 d2 / q)
        else 0))
    = ∑ e1 ∈ (envelopingPrimeProduct w z).divisors,
        ∑ e2 ∈ (envelopingPrimeProduct w z).divisors,
        (if (e1 : ℝ) ≤ z then envelopingH w e1 else 0) *
          (if (e2 : ℝ) ≤ z then envelopingH w e2 else 0) *
          (∑ d1 ∈ (envelopingPrimeProduct w z).divisors.filter (fun d => d ∣ e1),
            ∑ d2 ∈ (envelopingPrimeProduct w z).divisors.filter (fun d => d ∣ e2),
            (if q ∣ Nat.lcm d1 d2 then
              (ArithmeticFunction.moebius d1 : ℝ) * (ArithmeticFunction.moebius d2 : ℝ) *
                envelopingDensity w (Nat.lcm d1 d2 / q)
            else 0) / (envelopingDensity w d1 * envelopingDensity w d2)) := by
  set D := (envelopingPrimeProduct w z).divisors with hD
  -- abbreviation for the local coefficient
  set c : ℕ → ℕ → ℝ := fun d1 d2 =>
    (if q ∣ Nat.lcm d1 d2 then
      (ArithmeticFunction.moebius d1 : ℝ) * (ArithmeticFunction.moebius d2 : ℝ) *
        envelopingDensity w (Nat.lcm d1 d2 / q)
    else 0) / (envelopingDensity w d1 * envelopingDensity w d2) with hc
  -- step 1: expand each summand
  have hstep1 : ∀ d1 ∈ D, ∀ d2 ∈ D,
      (if q ∣ Nat.lcm d1 d2 then
          (ArithmeticFunction.moebius d1 : ℝ) * envelopingG w d1 z *
            ((ArithmeticFunction.moebius d2 : ℝ) * envelopingG w d2 z) *
            envelopingDensity w (Nat.lcm d1 d2 / q)
        else 0)
      = ∑ e1 ∈ D, ∑ e2 ∈ D,
          (if d1 ∣ e1 then (if (e1 : ℝ) ≤ z then envelopingH w e1 else 0) else 0) *
          (if d2 ∣ e2 then (if (e2 : ℝ) ≤ z then envelopingH w e2 else 0) else 0) *
          c d1 d2 := fun d1 hd1 d2 hd2 => vdc_expand hw hz hd1 hd2
  rw [Finset.sum_congr rfl (fun d1 hd1 => Finset.sum_congr rfl (fun d2 hd2 => hstep1 d1 hd1 d2 hd2))]
  -- step 2: permute the four sums
  have hperm : (∑ d1 ∈ D, ∑ d2 ∈ D, ∑ e1 ∈ D, ∑ e2 ∈ D,
        (if d1 ∣ e1 then (if (e1 : ℝ) ≤ z then envelopingH w e1 else 0) else 0) *
        (if d2 ∣ e2 then (if (e2 : ℝ) ≤ z then envelopingH w e2 else 0) else 0) * c d1 d2)
      = ∑ e1 ∈ D, ∑ e2 ∈ D, ∑ d1 ∈ D, ∑ d2 ∈ D,
        (if d1 ∣ e1 then (if (e1 : ℝ) ≤ z then envelopingH w e1 else 0) else 0) *
        (if d2 ∣ e2 then (if (e2 : ℝ) ≤ z then envelopingH w e2 else 0) else 0) * c d1 d2 := by
    have h1 : ∀ d1, (∑ d2 ∈ D, ∑ e1 ∈ D, ∑ e2 ∈ D,
        (if d1 ∣ e1 then (if (e1 : ℝ) ≤ z then envelopingH w e1 else 0) else 0) *
        (if d2 ∣ e2 then (if (e2 : ℝ) ≤ z then envelopingH w e2 else 0) else 0) * c d1 d2)
        = ∑ e1 ∈ D, ∑ d2 ∈ D, ∑ e2 ∈ D,
        (if d1 ∣ e1 then (if (e1 : ℝ) ≤ z then envelopingH w e1 else 0) else 0) *
        (if d2 ∣ e2 then (if (e2 : ℝ) ≤ z then envelopingH w e2 else 0) else 0) * c d1 d2 := by
      intro d1; rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun d1 _ => h1 d1), Finset.sum_comm]
    have h3 : ∀ e1, (∑ d1 ∈ D, ∑ d2 ∈ D, ∑ e2 ∈ D,
        (if d1 ∣ e1 then (if (e1 : ℝ) ≤ z then envelopingH w e1 else 0) else 0) *
        (if d2 ∣ e2 then (if (e2 : ℝ) ≤ z then envelopingH w e2 else 0) else 0) * c d1 d2)
        = ∑ d1 ∈ D, ∑ e2 ∈ D, ∑ d2 ∈ D,
        (if d1 ∣ e1 then (if (e1 : ℝ) ≤ z then envelopingH w e1 else 0) else 0) *
        (if d2 ∣ e2 then (if (e2 : ℝ) ≤ z then envelopingH w e2 else 0) else 0) * c d1 d2 := by
      intro e1; apply Finset.sum_congr rfl; intro d1 _; rw [Finset.sum_comm]
    simp only [h3]
    have h5 : ∀ e1, (∑ d1 ∈ D, ∑ e2 ∈ D, ∑ d2 ∈ D,
        (if d1 ∣ e1 then (if (e1 : ℝ) ≤ z then envelopingH w e1 else 0) else 0) *
        (if d2 ∣ e2 then (if (e2 : ℝ) ≤ z then envelopingH w e2 else 0) else 0) * c d1 d2)
        = ∑ e2 ∈ D, ∑ d1 ∈ D, ∑ d2 ∈ D,
        (if d1 ∣ e1 then (if (e1 : ℝ) ≤ z then envelopingH w e1 else 0) else 0) *
        (if d2 ∣ e2 then (if (e2 : ℝ) ≤ z then envelopingH w e2 else 0) else 0) * c d1 d2 := by
      intro e1; rw [Finset.sum_comm]
    simp only [h5]
  rw [hperm]
  -- step 3: factor the constants out of the inner sums
  apply Finset.sum_congr rfl
  intro e1 he1
  apply Finset.sum_congr rfl
  intro e2 he2
  have hin : (∑ d1 ∈ D.filter (fun d => d ∣ e1), ∑ d2 ∈ D.filter (fun d => d ∣ e2), c d1 d2)
      = ∑ d1 ∈ D, (if d1 ∣ e1 then (∑ d2 ∈ D, (if d2 ∣ e2 then c d1 d2 else 0)) else 0) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d1 _
    by_cases h1 : d1 ∣ e1
    · rw [if_pos h1, if_pos h1, Finset.sum_filter]
    · rw [if_neg h1, if_neg h1]
  have hR : (∑ d1 ∈ D.filter (fun d => d ∣ e1), ∑ d2 ∈ D.filter (fun d => d ∣ e2),
        (if (e1 : ℝ) ≤ z then envelopingH w e1 else 0) *
          (if (e2 : ℝ) ≤ z then envelopingH w e2 else 0) * c d1 d2)
      = ∑ d1 ∈ D, ∑ d2 ∈ D,
          (if d1 ∣ e1 then (if (e1 : ℝ) ≤ z then envelopingH w e1 else 0) else 0) *
          (if d2 ∣ e2 then (if (e2 : ℝ) ≤ z then envelopingH w e2 else 0) else 0) * c d1 d2 := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d1 _
    rw [Finset.sum_filter]
    by_cases h1 : d1 ∣ e1
    · simp only [if_pos h1]
      apply Finset.sum_congr rfl
      intro d2 _
      by_cases h2 : d2 ∣ e2 <;> simp [h2] <;> ring
    · simp only [if_neg h1]
      simp
  rw [← hR]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]


/-- Indicator sums over subsets restrict to subsets of a smaller set. -/
private theorem vdc_sum_indicator {s t : Finset ℕ} (ht : t ⊆ s) (G : Finset ℕ → ℝ) :
    (∑ u ∈ s.powerset, (if u ⊆ t then G u else 0)) = ∑ u ∈ t.powerset, G u := by
  rw [← Finset.sum_filter]
  congr 1
  ext u
  simp only [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun h => h.2, fun h => ⟨Finset.Subset.trans h ht, h⟩⟩

/-- The divisors of `e` inside the divisor set of a nonzero multiple. -/
private theorem vdc_filter_divisors {P' e : ℕ} (he : e ∣ P') (hP : P' ≠ 0) :
    P'.divisors.filter (fun d => d ∣ e) = e.divisors := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hdP, -⟩, hde⟩
    refine ⟨hde, fun h => hP ?_⟩
    rw [h] at he
    exact Nat.eq_zero_of_zero_dvd he
  · rintro ⟨hde, -⟩
    exact ⟨⟨hde.trans he, hP⟩, hde⟩

/-- The indicator of two subset inclusions as a product of local conditions. -/
private theorem vdc_ind_prod {s t1 t2 u1 u2 : Finset ℕ} (hu1 : u1 ⊆ s) (hu2 : u2 ⊆ s)
    (ht1 : t1 ⊆ s) (ht2 : t2 ⊆ s) (φ : ℕ → Bool → Bool → ℝ) :
    (if u1 ⊆ t1 ∧ u2 ⊆ t2 then ∏ p ∈ s, φ p (p ∈ u1) (p ∈ u2) else 0)
      = ∏ p ∈ s, (if (p ∈ u1 → p ∈ t1) ∧ (p ∈ u2 → p ∈ t2) then φ p (p ∈ u1) (p ∈ u2) else 0) := by
  by_cases H : u1 ⊆ t1 ∧ u2 ⊆ t2
  · rw [if_pos H]
    apply Finset.prod_congr rfl
    intro p hp
    rw [if_pos ⟨fun h => H.1 h, fun h => H.2 h⟩]
  · rw [if_neg H]
    have hex : ∃ p ∈ s, ¬ ((p ∈ u1 → p ∈ t1) ∧ (p ∈ u2 → p ∈ t2)) := by
      by_contra hc
      push_neg at hc
      exact H ⟨fun x hx => (hc x (hu1 hx)).1 hx, fun x hx => (hc x (hu2 hx)).2 hx⟩
    obtain ⟨p, hp, hnp⟩ := hex
    exact (Finset.prod_eq_zero hp (if_neg hnp)).symm

/-- Value of the restricted local sum at the four possibilities. -/
private theorem vdc_local {w q : ℕ} {p : ℕ} {t1 t2 : Finset ℕ}
    (ha : (envelopingOmega w p : ℝ) / p ≠ 0) :
    (if (p ∈ t1 ∧ p ∈ t2) then
        (-(1 : ℝ) / ((envelopingOmega w p : ℝ) / p)) * (-(1 : ℝ) / ((envelopingOmega w p : ℝ) / p)) *
          (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) else 0)
      + (if p ∈ t1 then
          (-(1 : ℝ) / ((envelopingOmega w p : ℝ) / p)) * 1 *
            (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) else 0)
      + (if p ∈ t2 then
          1 * (-(1 : ℝ) / ((envelopingOmega w p : ℝ) / p)) *
            (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) else 0)
      + (1 * 1 * (if p ∣ q then (0 : ℝ) else 1))
      = ((if p ∈ t1 ∧ p ∈ t2 then
            (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
              ((envelopingOmega w p : ℝ) / p) ^ 2 else 0)
          + (if p ∈ t1 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∈ t2 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∣ q then (0 : ℝ) else 1)) := by
  by_cases h1 : p ∈ t1 <;> by_cases h2 : p ∈ t2 <;> by_cases h3 : p ∣ q <;>
    simp only [h1, h2, h3, if_true, if_false, and_self, and_false] <;>
    field_simp <;> ring


/-- The local weight `H` at a prime is `a/(1-a)` in terms of `a = omega/p`. -/
private theorem vdc_H_prime {w : ℕ} {z : ℝ} {p : ℕ} (hw : 5 ≤ w)
    (hp : p ∈ (envelopingPrimeProduct w z).primeFactors) :
    envelopingH w p = ((envelopingOmega w p : ℝ) / p) / (1 - (envelopingOmega w p : ℝ) / p) := by
  have hpp := vdc_prime hp
  have hwp : w < p := efs_prime_gt hpp (Nat.dvd_of_mem_primeFactors hp)
  have hom2 : envelopingOmega w p ≤ 2 := by
    unfold envelopingOmega
    rw [if_neg (by omega : ¬ p ≤ w)]
    split_ifs <;> omega
  have hlep : envelopingOmega w p ≤ p := by
    have : (6 : ℕ) ≤ p := by omega
    omega
  unfold envelopingH
  rw [if_pos hpp.squarefree, hpp.primeFactors, Finset.prod_singleton, Nat.cast_sub hlep]
  have h2 : (envelopingOmega w p : ℝ) ≤ 2 := by exact_mod_cast hom2
  have hp6 : (6 : ℝ) ≤ p := by exact_mod_cast (show 6 ≤ p by omega)
  have hp0 : (0:ℝ) < p := by linarith
  have hlt : ((envelopingOmega w p : ℝ)) < p := by linarith
  have hpos : (0:ℝ) < 1 - (envelopingOmega w p : ℝ) / p := by
    rw [sub_pos, div_lt_one hp0]
    linarith
  have hpne : (p : ℝ) ≠ 0 := by linarith
  field_simp
  try ring

/-- Absolute value of the local factor off the primes of `q`. -/
private theorem vdc_abs_off {w q : ℕ} {z : ℝ} {p : ℕ} {t1 t2 : Finset ℕ} (hw : 5 ≤ w)
    (hp : p ∈ (envelopingPrimeProduct w z).primeFactors) (hpq : ¬ p ∣ q) :
    (if p ∈ t1 then envelopingH w p else 1) * (if p ∈ t2 then envelopingH w p else 1) *
      |((if p ∈ t1 ∧ p ∈ t2 then
            (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
              ((envelopingOmega w p : ℝ) / p) ^ 2 else 0)
          + (if p ∈ t1 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∈ t2 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∣ q then (0 : ℝ) else 1))|
      = (if p ∈ t1 ∧ p ∈ t2 then envelopingH w p
          else if p ∈ t1 ∨ p ∈ t2 then 0 else 1) := by
  have hH := vdc_H_prime hw hp
  have hwp : w < p := efs_prime_gt (vdc_prime hp) (Nat.dvd_of_mem_primeFactors hp)
  have hom1 : 1 ≤ envelopingOmega w p := by
    unfold envelopingOmega
    rw [if_neg (by omega : ¬ p ≤ w)]
    split_ifs <;> omega
  have hom2 : envelopingOmega w p ≤ 2 := by
    unfold envelopingOmega
    rw [if_neg (by omega : ¬ p ≤ w)]
    split_ifs <;> omega
  have ha1 : (1 : ℝ) ≤ (envelopingOmega w p : ℝ) := by exact_mod_cast hom1
  have ha2 : (envelopingOmega w p : ℝ) ≤ 2 := by exact_mod_cast hom2
  have h6 : (6 : ℝ) ≤ p := by
    have : (6 : ℕ) ≤ p := by omega
    exact_mod_cast this
  have hp0 : (0 : ℝ) < p := by linarith
  set a : ℝ := (envelopingOmega w p : ℝ) / p with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  have halt : a < 1 := by
    rw [ha, div_lt_one hp0]; linarith
  have hane : a ≠ 0 := ne_of_gt ha0
  by_cases h1 : p ∈ t1
  · by_cases h2 : p ∈ t2
    · simp only [h1, h2, if_true, and_self, or_self, hpq, if_false, or_true, true_or]
      have hv : a / a ^ 2 + -(a / a) + -(a / a) + 1 = 1 / a - 1 := by
        field_simp
        ring
      have hpos : (0 : ℝ) < 1 / a - 1 := by
        have h2' : 1 < 1 / a := by rw [one_lt_div ha0]; linarith
        linarith
      rw [hv, abs_of_pos hpos, hH, ha]
      field_simp
      try ring
    · simp only [h1, h2, if_true, if_false, and_false, or_false, false_or, hpq, and_true]
      have hz : (0 : ℝ) + -(a / a) + 0 + 1 = 0 := by
        field_simp
        try ring
      rw [hz, abs_zero]
      ring
  · by_cases h2 : p ∈ t2
    · simp only [h1, h2, if_true, if_false, and_false, or_false, false_or, hpq, and_true]
      have hz : (0 : ℝ) + 0 + -(a / a) + 1 = 0 := by
        field_simp
        try ring
      rw [hz, abs_zero]
      ring
    · simp only [h1, h2, if_false, and_false, or_self, or_false, false_or, hpq]
      norm_num


/-- Absolute value of the local factor at the primes of `q`. -/
private theorem vdc_abs_qs {w q : ℕ} {z : ℝ} {p : ℕ} {t1 t2 : Finset ℕ} (hw : 5 ≤ w)
    (hp : p ∈ (envelopingPrimeProduct w z).primeFactors) (hpq : p ∣ q) :
    (if p ∈ t1 then envelopingH w p else 1) * (if p ∈ t2 then envelopingH w p else 1) *
      |((if p ∈ t1 ∧ p ∈ t2 then
            (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
              ((envelopingOmega w p : ℝ) / p) ^ 2 else 0)
          + (if p ∈ t1 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∈ t2 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∣ q then (0 : ℝ) else 1))|
      = (if p ∈ t1 ∧ p ∈ t2 then
          (1 - 2 * ((envelopingOmega w p : ℝ) / p)) / (1 - (envelopingOmega w p : ℝ) / p) ^ 2
          else if p ∈ t1 ∨ p ∈ t2 then 1 / (1 - (envelopingOmega w p : ℝ) / p) else 0) := by
  have hH := vdc_H_prime hw hp
  have hwp : w < p := efs_prime_gt (vdc_prime hp) (Nat.dvd_of_mem_primeFactors hp)
  have hom1 : 1 ≤ envelopingOmega w p := by
    unfold envelopingOmega
    rw [if_neg (by omega : ¬ p ≤ w)]
    split_ifs <;> omega
  have hom2 : envelopingOmega w p ≤ 2 := by
    unfold envelopingOmega
    rw [if_neg (by omega : ¬ p ≤ w)]
    split_ifs <;> omega
  have ha1 : (1 : ℝ) ≤ (envelopingOmega w p : ℝ) := by exact_mod_cast hom1
  have ha2 : (envelopingOmega w p : ℝ) ≤ 2 := by exact_mod_cast hom2
  have h6 : (6 : ℝ) ≤ p := by
    have : (6 : ℕ) ≤ p := by omega
    exact_mod_cast this
  have hp0 : (0 : ℝ) < p := by linarith
  set a : ℝ := (envelopingOmega w p : ℝ) / p with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  have halt : a < 1 / 2 := by
    rw [ha, div_lt_iff₀ hp0]
    nlinarith
  have hane : a ≠ 0 := ne_of_gt ha0
  by_cases h1 : p ∈ t1
  · by_cases h2 : p ∈ t2
    · simp only [h1, h2, if_true, and_self, or_self, hpq, if_false, or_true, true_or]
      have hv : 1 / a ^ 2 + -(1 / a) + -(1 / a) + 0 = (1 - 2 * a) / a ^ 2 := by
        field_simp
        ring
      have hnn : (0 : ℝ) ≤ (1 - 2 * a) / a ^ 2 := by
        apply div_nonneg _ (by positivity)
        linarith
      rw [hv, abs_of_nonneg hnn, hH, ha]
      field_simp
      try ring
    · simp only [h1, h2, if_true, if_false, and_false, or_false, false_or, hpq, and_true]
      have hv : (0 : ℝ) + -(1 / a) + 0 + 0 = -(1 / a) := by ring
      rw [hv, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 1 / a), hH, ha]
      field_simp
      try ring
  · by_cases h2 : p ∈ t2
    · simp only [h1, h2, if_true, if_false, and_false, or_false, false_or, hpq, and_true]
      have hv : (0 : ℝ) + 0 + -(1 / a) + 0 = -(1 / a) := by ring
      rw [hv, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 1 / a), hH, ha]
      field_simp
      try ring
    · simp only [h1, h2, if_false, and_false, or_self, or_false, false_or, hpq, reduceIte]
      norm_num

/-- The inner twisted sum factorises over the primes of the support. -/
private theorem vdc_psi_factor {w q : ℕ} (hw : 5 ≤ w) {z : ℝ}
    (hq : q ∣ envelopingPrimeProduct w z) {e1 e2 : ℕ}
    (he1 : e1 ∈ (envelopingPrimeProduct w z).divisors)
    (he2 : e2 ∈ (envelopingPrimeProduct w z).divisors) :
    (∑ d1 ∈ (envelopingPrimeProduct w z).divisors.filter (fun d => d ∣ e1),
        ∑ d2 ∈ (envelopingPrimeProduct w z).divisors.filter (fun d => d ∣ e2),
        (if q ∣ Nat.lcm d1 d2 then
          (ArithmeticFunction.moebius d1 : ℝ) * (ArithmeticFunction.moebius d2 : ℝ) *
            envelopingDensity w (Nat.lcm d1 d2 / q)
        else 0) / (envelopingDensity w d1 * envelopingDensity w d2))
    = ∏ p ∈ (envelopingPrimeProduct w z).primeFactors,
        ((if p ∈ e1.primeFactors ∧ p ∈ e2.primeFactors then
            (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
              ((envelopingOmega w p : ℝ) / p) ^ 2 else 0)
          + (if p ∈ e1.primeFactors then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∈ e2.primeFactors then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∣ q then (0 : ℝ) else 1)) := by

  set s : Finset ℕ := (envelopingPrimeProduct w z).primeFactors with hs
  set P' : ℕ := envelopingPrimeProduct w z with hP'
  have hP0 : P' ≠ 0 := envelopingPrimeProduct_ne_zero w z
  have hsqP : Squarefree P' := vdc_P_sqfree hw z
  have ht1 : e1.primeFactors ⊆ s := by
    rw [hs]; exact Nat.primeFactors_mono (Nat.dvd_of_mem_divisors he1) hP0
  have ht2 : e2.primeFactors ⊆ s := by
    rw [hs]; exact Nat.primeFactors_mono (Nat.dvd_of_mem_divisors he2) hP0
  have he1P : e1 ∣ P' := Nat.dvd_of_mem_divisors he1
  have he2P : e2 ∣ P' := Nat.dvd_of_mem_divisors he2
  have hp1 : ∀ p ∈ e1.primeFactors, p.Prime := fun p hp => vdc_prime (ht1 hp)
  have hp2 : ∀ p ∈ e2.primeFactors, p.Prime := fun p hp => vdc_prime (ht2 hp)
  have hsq1 : Squarefree e1 := hsqP.squarefree_of_dvd he1P
  have hsq2 : Squarefree e2 := hsqP.squarefree_of_dvd he2P
  have hA : ∀ p ∈ s, (envelopingOmega w p : ℝ) / p ≠ 0 := by
    intro p hp
    have h := vdc_omega_pos (hs ▸ hp)
    have hp' : (0:ℝ) < p := by exact_mod_cast (vdc_prime (hs ▸ hp)).pos
    positivity
  -- (A) the filtered divisor sums become subset sums over the prime factors
  have stepA : (∑ d1 ∈ P'.divisors.filter (fun d => d ∣ e1),
        ∑ d2 ∈ P'.divisors.filter (fun d => d ∣ e2),
        (if q ∣ Nat.lcm d1 d2 then
          (ArithmeticFunction.moebius d1 : ℝ) * (ArithmeticFunction.moebius d2 : ℝ) *
            envelopingDensity w (Nat.lcm d1 d2 / q)
        else 0) / (envelopingDensity w d1 * envelopingDensity w d2))
      = ∑ u1 ∈ e1.primeFactors.powerset, ∑ u2 ∈ e2.primeFactors.powerset,
        (if q ∣ Nat.lcm (∏ p ∈ u1, p) (∏ p ∈ u2, p) then
          (ArithmeticFunction.moebius (∏ p ∈ u1, p) : ℝ) *
              (ArithmeticFunction.moebius (∏ p ∈ u2, p) : ℝ) *
            envelopingDensity w (Nat.lcm (∏ p ∈ u1, p) (∏ p ∈ u2, p) / q)
        else 0) / (envelopingDensity w (∏ p ∈ u1, p) * envelopingDensity w (∏ p ∈ u2, p)) := by
    rw [vdc_filter_divisors he1P hP0, vdc_filter_divisors he2P hP0]
    rw [sel_sum_divisors hsq1]
    apply Finset.sum_congr rfl
    intro u1 hu1
    rw [sel_sum_divisors hsq2]
  -- (B) extend the sums to the whole support, with inclusion indicators
  have hB : (∑ u1 ∈ e1.primeFactors.powerset, ∑ u2 ∈ e2.primeFactors.powerset,
        (if q ∣ Nat.lcm (∏ p ∈ u1, p) (∏ p ∈ u2, p) then
          (ArithmeticFunction.moebius (∏ p ∈ u1, p) : ℝ) *
              (ArithmeticFunction.moebius (∏ p ∈ u2, p) : ℝ) *
            envelopingDensity w (Nat.lcm (∏ p ∈ u1, p) (∏ p ∈ u2, p) / q)
        else 0) / (envelopingDensity w (∏ p ∈ u1, p) * envelopingDensity w (∏ p ∈ u2, p)))
      = ∑ u1 ∈ s.powerset, ∑ u2 ∈ s.powerset,
          (if u1 ⊆ e1.primeFactors then
            (if u2 ⊆ e2.primeFactors then
              (if q ∣ Nat.lcm (∏ p ∈ u1, p) (∏ p ∈ u2, p) then
                (ArithmeticFunction.moebius (∏ p ∈ u1, p) : ℝ) *
                    (ArithmeticFunction.moebius (∏ p ∈ u2, p) : ℝ) *
                  envelopingDensity w (Nat.lcm (∏ p ∈ u1, p) (∏ p ∈ u2, p) / q)
              else 0) / (envelopingDensity w (∏ p ∈ u1, p) * envelopingDensity w (∏ p ∈ u2, p))
            else 0) else 0) := by
    rw [← vdc_sum_indicator ht1]
    apply Finset.sum_congr rfl
    intro u1 _
    by_cases h : u1 ⊆ e1.primeFactors
    · simp only [if_pos h]
      exact (vdc_sum_indicator ht2 _).symm
    · simp only [if_neg h]
      simp
  -- (C) each summand is the product of the restricted local factors
  have stepC : (∑ u1 ∈ s.powerset, ∑ u2 ∈ s.powerset,
        (if u1 ⊆ e1.primeFactors then
          (if u2 ⊆ e2.primeFactors then
            (if q ∣ Nat.lcm (∏ p ∈ u1, p) (∏ p ∈ u2, p) then
              (ArithmeticFunction.moebius (∏ p ∈ u1, p) : ℝ) *
                  (ArithmeticFunction.moebius (∏ p ∈ u2, p) : ℝ) *
                envelopingDensity w (Nat.lcm (∏ p ∈ u1, p) (∏ p ∈ u2, p) / q)
            else 0) / (envelopingDensity w (∏ p ∈ u1, p) * envelopingDensity w (∏ p ∈ u2, p))
          else 0) else 0))
      = ∑ u1 ∈ s.powerset, ∑ u2 ∈ s.powerset, ∏ p ∈ s,
          (if (p ∈ u1 → p ∈ e1.primeFactors) ∧ (p ∈ u2 → p ∈ e2.primeFactors) then
            (if p ∈ u1 then -(1 : ℝ) / ((envelopingOmega w p : ℝ) / p) else 1)
              * (if p ∈ u2 then -(1 : ℝ) / ((envelopingOmega w p : ℝ) / p) else 1)
              * (if p ∈ u1 ∨ p ∈ u2 then (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p)
                 else (if p ∣ q then (0 : ℝ) else 1))
          else 0) := by
    apply Finset.sum_congr rfl
    intro u1 hu1
    apply Finset.sum_congr rfl
    intro u2 hu2
    have hu1s : u1 ⊆ s := Finset.mem_powerset.mp hu1
    have hu2s : u2 ⊆ s := Finset.mem_powerset.mp hu2
    have hW := vdc_weight_factor hu1s hu2s hq
    by_cases h1 : u1 ⊆ e1.primeFactors
    · by_cases h2 : u2 ⊆ e2.primeFactors
      · simp only [if_pos h1, if_pos h2]
        rw [hW, hs]
        apply Finset.prod_congr rfl
        intro p _
        rw [if_pos (show (p ∈ u1 → p ∈ e1.primeFactors) ∧ (p ∈ u2 → p ∈ e2.primeFactors)
          from ⟨fun hp => h1 hp, fun hp => h2 hp⟩)]
      · simp only [if_pos h1, if_neg h2]
        obtain ⟨p0, hp0u2, hp0t2⟩ := Finset.not_subset.mp h2
        refine (Finset.prod_eq_zero (hu2s hp0u2) ?_).symm
        rw [if_neg]
        intro hh
        exact hp0t2 (hh.2 hp0u2)
    · simp only [if_neg h1]
      obtain ⟨p0, hp0u1, hp0t1⟩ := Finset.not_subset.mp h1
      refine (Finset.prod_eq_zero (hu1s hp0u1) ?_).symm
      rw [if_neg]
      intro hh
      exact hp0t1 (hh.1 hp0u1)
  rw [stepA, hB, stepC]
  -- (D) convert the local factors to `decide` form and read off the product of local sums
  have hconv : ∀ u1 u2 : Finset ℕ,
      (∏ p ∈ s,
        (if (p ∈ u1 → p ∈ e1.primeFactors) ∧ (p ∈ u2 → p ∈ e2.primeFactors) then
          (if p ∈ u1 then -(1 : ℝ) / ((envelopingOmega w p : ℝ) / p) else 1)
            * (if p ∈ u2 then -(1 : ℝ) / ((envelopingOmega w p : ℝ) / p) else 1)
            * (if p ∈ u1 ∨ p ∈ u2 then (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p)
               else (if p ∣ q then (0 : ℝ) else 1))
        else 0))
      = ∏ p ∈ s,
        (fun p i j =>
          if (i = true → p ∈ e1.primeFactors) ∧ (j = true → p ∈ e2.primeFactors) then
            (if i then -(1 : ℝ) / ((envelopingOmega w p : ℝ) / p) else 1)
              * (if j then -(1 : ℝ) / ((envelopingOmega w p : ℝ) / p) else 1)
              * (if i ∨ j then (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p)
                 else (if p ∣ q then (0 : ℝ) else 1))
          else 0) p (decide (p ∈ u1)) (decide (p ∈ u2)) := by
    intro u1 u2
    apply Finset.prod_congr rfl
    intro p _
    simp
  simp only [hconv]
  rw [← vdc_pair_prod s (fun p i j =>
    if (i = true → p ∈ e1.primeFactors) ∧ (j = true → p ∈ e2.primeFactors) then
      (if i then -(1 : ℝ) / ((envelopingOmega w p : ℝ) / p) else 1)
        * (if j then -(1 : ℝ) / ((envelopingOmega w p : ℝ) / p) else 1)
        * (if i ∨ j then (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p)
           else (if p ∣ q then (0 : ℝ) else 1))
    else 0)]
  apply Finset.prod_congr rfl
  intro p hp
  simp only [reduceIte, if_true, if_false, Bool.false_eq_true, Bool.true_eq_false, or_self,
    and_self, true_implies, false_implies, and_true, true_and, and_false, false_and, or_true,
    true_or, decide_true, reduceCtorEq]
  exact vdc_local (q := q) (p := p) (t1 := e1.primeFactors) (t2 := e2.primeFactors) (hA p hp)

/-- The mass of `H` over the divisors at most `z` is at most `G 1`. -/
private theorem vdc_mass {w : ℕ} (hw : 5 ≤ w) {z : ℝ} (hz : 1 ≤ z) :
    (∑ n ∈ (envelopingPrimeProduct w z).primeFactors.powerset,
        (if ((∏ p ∈ n, p : ℕ) : ℝ) ≤ z then envelopingH w (∏ p ∈ n, p) else 0))
      ≤ envelopingG w 1 z := by
  rw [← sel_sum_divisors (vdc_P_sqfree hw z) (fun e => if (e : ℝ) ≤ z then envelopingH w e else 0),
    sel_G1 w hw z hz]

/-- `H` is at most one at primes of the support. -/
private theorem vdc_H_le_one {w : ℕ} {z : ℝ} {p : ℕ} (hw : 5 ≤ w)
    (hp : p ∈ (envelopingPrimeProduct w z).primeFactors) : envelopingH w p ≤ 1 := by
  rw [vdc_H_prime hw hp]
  have hpp := vdc_prime hp
  have hwp : w < p := efs_prime_gt hpp (Nat.dvd_of_mem_primeFactors hp)
  have h5 : 5 < p := by omega
  have hom1 : 1 ≤ envelopingOmega w p := by
    unfold envelopingOmega
    rw [if_neg (by omega : ¬ p ≤ w)]
    split_ifs <;> omega
  have ha1 : (1 : ℝ) ≤ (envelopingOmega w p : ℝ) := by exact_mod_cast hom1
  have hom2 : envelopingOmega w p ≤ 2 := by
    unfold envelopingOmega
    rw [if_neg (by omega : ¬ p ≤ w)]
    split_ifs <;> omega
  have ha2 : (envelopingOmega w p : ℝ) ≤ 2 := by exact_mod_cast hom2
  have hp6 : (6 : ℝ) ≤ p := by exact_mod_cast (show 6 ≤ p by omega)
  have hp0 : (0 : ℝ) < p := by linarith
  have hapos : (0 : ℝ) < (envelopingOmega w p : ℝ) / p := by positivity
  have hlt : (envelopingOmega w p : ℝ) / p ≤ 1 / 2 := by
    rw [div_le_iff₀ hp0]; nlinarith
  rw [div_le_one (by linarith)]
  linarith


/-- The product of the off-`q` local bounds is the mass of the common part. -/
private theorem vdc_off_prod {w : ℕ} {s off qs n1 n2 : Finset ℕ}
    (hu : off ∪ qs = s) (hd : Disjoint off qs) (hn1 : n1 ⊆ off) (hn2 : n2 ⊆ off) :
    ∏ p ∈ s \ qs, (if p ∈ n1 ∧ p ∈ n2 then envelopingH w p
        else if p ∈ n1 ∨ p ∈ n2 then (0 : ℝ) else 1)
      = (if n1 = n2 then ∏ p ∈ n1, envelopingH w p else 0) := by
  have hso : s \ qs = off := by
    rw [← hu, Finset.union_sdiff_cancel_right hd]
  rw [hso]
  by_cases h : n1 = n2
  · rw [if_pos h, h]
    have hsimp : ∀ p, (if p ∈ n2 ∧ p ∈ n2 then envelopingH w p
        else if p ∈ n2 ∨ p ∈ n2 then (0:ℝ) else 1)
        = (if p ∈ n2 then envelopingH w p else 1) := by
      intro p
      by_cases h1 : p ∈ n2 <;> simp [h1]
    simp only [hsimp]
    rw [← vdc_prod_ite_mem_single hn2]
  · rw [if_neg h]
    have hex : ∃ p, (p ∈ n1 ∧ p ∉ n2) ∨ (p ∈ n2 ∧ p ∉ n1) := by
      by_cases hs1 : n1 ⊆ n2
      · have hs2 : ¬ n2 ⊆ n1 := fun h2 => h (Finset.Subset.antisymm hs1 h2)
        obtain ⟨p, hp2, hp1⟩ := Finset.not_subset.mp hs2
        exact ⟨p, Or.inr ⟨hp2, hp1⟩⟩
      · obtain ⟨p, hp1, hp2⟩ := Finset.not_subset.mp hs1
        exact ⟨p, Or.inl ⟨hp1, hp2⟩⟩
    obtain ⟨p, hp⟩ := hex
    refine Finset.prod_eq_zero (i := p) ?_ ?_
    · rcases hp with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hn1 h1
      · exact hn2 h1
    · rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]


/-- Arithmetic at a prime of `q`. -/
private theorem vdc_qs_arith {w : ℕ} {z : ℝ} {p : ℕ} (hw : 5 ≤ w)
    (hp : p ∈ (envelopingPrimeProduct w z).primeFactors) :
    2 / (1 - (envelopingOmega w p : ℝ) / p)
      + (1 - 2 * ((envelopingOmega w p : ℝ) / p)) / (1 - (envelopingOmega w p : ℝ) / p) ^ 2
      ≤ 4 := by
  have hpp := vdc_prime hp
  have hwp : w < p := efs_prime_gt hpp (Nat.dvd_of_mem_primeFactors hp)
  have h5 : 5 < p := by omega
  have hom1 : 1 ≤ envelopingOmega w p := by
    unfold envelopingOmega
    rw [if_neg (by omega : ¬ p ≤ w)]
    split_ifs <;> omega
  have hom2 : envelopingOmega w p ≤ 2 := by
    unfold envelopingOmega
    rw [if_neg (by omega : ¬ p ≤ w)]
    split_ifs <;> omega
  have ha1 : (1 : ℝ) ≤ (envelopingOmega w p : ℝ) := by exact_mod_cast hom1
  have ha2 : (envelopingOmega w p : ℝ) ≤ 2 := by exact_mod_cast hom2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hp6 : (6 : ℝ) ≤ p := by exact_mod_cast (show 6 ≤ p by omega)
  have hlt : (envelopingOmega w p : ℝ) / p ≤ 1 / 3 := by
    rw [div_le_iff₀ hp0]; linarith
  set a := (envelopingOmega w p : ℝ) / p with ha
  have h1a : 0 < 1 - a := by linarith
  have hane : (1 - a) ≠ 0 := ne_of_gt h1a
  have key : 2 / (1 - a) + (1 - 2 * a) / (1 - a) ^ 2
      = (2 * (1 - a) + (1 - 2 * a)) / (1 - a) ^ 2 := by
    field_simp
    try ring
  rw [key]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < (1 - a) ^ 2)]
  nlinarith [sq_nonneg (1 - 2 * a)]

/-- `H` is nonnegative. -/
private theorem vdc_H_nonneg (w d : ℕ) : 0 ≤ envelopingH w d := by
  unfold envelopingH
  split_ifs
  · exact Finset.prod_nonneg (fun p _ => by positivity)
  · exact le_rfl

/-- `G` at one is positive, since `H` at one is one. -/
private theorem vdc_G1_pos {w : ℕ} (hw : 5 ≤ w) {z : ℝ} (hz : 1 ≤ z) :
    0 < envelopingG w 1 z := by
  rw [sel_G1 w hw z hz]
  have hmem : (1 : ℕ) ∈ (envelopingPrimeProduct w z).divisors :=
    Nat.mem_divisors.mpr ⟨one_dvd _, envelopingPrimeProduct_ne_zero w z⟩
  have hle := Finset.single_le_sum
    (f := fun e : ℕ => if (e : ℝ) ≤ z then envelopingH w e else 0)
    (fun i _ => by split_ifs with h <;> [exact vdc_H_nonneg w i; exact le_rfl]) hmem
  have hone : (if ((1 : ℕ) : ℝ) ≤ z then envelopingH w 1 else 0) = 1 := by
    rw [if_pos (by simpa using hz)]
    unfold envelopingH
    simp
  rw [hone] at hle
  linarith

/-- The Selberg coefficients multiply to the `mu G` form over `G 1` squared. -/
private theorem vdc_rho_mul {w : ℕ} {z : ℝ} {d1 d2 : ℕ} (hG : envelopingG w 1 z ≠ 0) :
    envelopingRho w d1 z * envelopingRho w d2 z =
      (ArithmeticFunction.moebius d1 : ℝ) * envelopingG w d1 z *
        ((ArithmeticFunction.moebius d2 : ℝ) * envelopingG w d2 z) /
          (envelopingG w 1 z) ^ 2 := by
  unfold envelopingRho
  field_simp

/-- A divisor of `P` given as a product over a set of primes of the support. -/
private theorem vdc_E_mem {w : ℕ} (hw : 5 ≤ w) {z : ℝ} {u : Finset ℕ}
    (hu : u ⊆ (envelopingPrimeProduct w z).primeFactors) :
    ∏ p ∈ u, p ∈ (envelopingPrimeProduct w z).divisors :=
  Nat.mem_divisors.mpr ⟨vdc_E_dvd hw hu, envelopingPrimeProduct_ne_zero w z⟩

/-- The prime factors of `E u` are `u` itself. -/
private theorem vdc_E_pf' {w : ℕ} {z : ℝ} {u : Finset ℕ}
    (hu : u ⊆ (envelopingPrimeProduct w z).primeFactors) :
    (∏ p ∈ u, p).primeFactors = u :=
  vdc_E_pf u (fun p hp => vdc_prime (hu hp))

/-- The local factor at a prime outside `q` reduces to a two-case weight. -/
private theorem vdc_A_off {w q : ℕ} (hw : 5 ≤ w) {z : ℝ} {p : ℕ}
    {t1 t2 n1 n2 : Finset ℕ} (hp : p ∈ (envelopingPrimeProduct w z).primeFactors)
    (hpq : ¬ p ∣ q) (hn1 : n1 ⊆ t1) (hn2 : n2 ⊆ t2)
    (hq1 : ∀ x ∈ t1, x ∉ n1 → x ∣ q) (hq2 : ∀ x ∈ t2, x ∉ n2 → x ∣ q) :
    (if p ∈ t1 then envelopingH w p else 1) * (if p ∈ t2 then envelopingH w p else 1) *
      |((if p ∈ t1 ∧ p ∈ t2 then
            (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
              ((envelopingOmega w p : ℝ) / p) ^ 2 else 0)
          + (if p ∈ t1 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∈ t2 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∣ q then (0 : ℝ) else 1))|
      = (if p ∈ n1 ∧ p ∈ n2 then envelopingH w p
          else if p ∈ n1 ∨ p ∈ n2 then 0 else 1) := by
  rw [vdc_abs_off (w := w) (q := q) (z := z) (p := p) (t1 := t1) (t2 := t2) hw hp hpq]
  have e1 : (p ∈ t1) ↔ (p ∈ n1) :=
    ⟨fun h => by
        by_contra h'
        exact hpq (hq1 p h h'),
      fun h => hn1 h⟩
  have e2 : (p ∈ t2) ↔ (p ∈ n2) :=
    ⟨fun h => by
        by_contra h'
        exact hpq (hq2 p h h'),
      fun h => hn2 h⟩
  simp only [e1, e2]

/-- The local factor at a prime of `q` reduces to a three-case weight. -/
private theorem vdc_A_qs {w q : ℕ} (hw : 5 ≤ w) {z : ℝ} {p : ℕ}
    {t1 t2 a1 a2 : Finset ℕ} (hp : p ∈ (envelopingPrimeProduct w z).primeFactors)
    (hpq : p ∣ q) (ha1 : a1 ⊆ t1) (ha2 : a2 ⊆ t2)
    (ho1 : ∀ x ∈ t1, x ∉ a1 → ¬ x ∣ q) (ho2 : ∀ x ∈ t2, x ∉ a2 → ¬ x ∣ q) :
    (if p ∈ t1 then envelopingH w p else 1) * (if p ∈ t2 then envelopingH w p else 1) *
      |((if p ∈ t1 ∧ p ∈ t2 then
            (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
              ((envelopingOmega w p : ℝ) / p) ^ 2 else 0)
          + (if p ∈ t1 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∈ t2 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∣ q then (0 : ℝ) else 1))|
      = (if p ∈ a1 ∧ p ∈ a2 then
          (1 - 2 * ((envelopingOmega w p : ℝ) / p)) / (1 - (envelopingOmega w p : ℝ) / p) ^ 2
          else if p ∈ a1 ∨ p ∈ a2 then 1 / (1 - (envelopingOmega w p : ℝ) / p) else 0) := by
  rw [vdc_abs_qs (w := w) (q := q) (z := z) (p := p) (t1 := t1) (t2 := t2) hw hp hpq]
  have e1 : (p ∈ t1) ↔ (p ∈ a1) :=
    ⟨fun h => by
        by_contra h'
        exact ho1 p h h' hpq,
      fun h => ha1 h⟩
  have e2 : (p ∈ t2) ↔ (p ∈ a2) :=
    ⟨fun h => by
        by_contra h'
        exact ho2 p h h' hpq,
      fun h => ha2 h⟩
  simp only [e1, e2]

/-- A product splits over a subset. -/
private theorem vdc_prod_sdiff_split {s qs : Finset ℕ} (h : qs ⊆ s) (f : ℕ → ℝ) :
    (∏ p ∈ s, f p) = (∏ p ∈ s \ qs, f p) * ∏ p ∈ qs, f p :=
  (Finset.prod_sdiff h).symm

/-- The twisted Selberg form as a double sum over the prime support with the local factors. -/
private theorem vdc_subset_form {w q : ℕ} (hw : 5 ≤ w) {z : ℝ} (hz : 1 ≤ z)
    (hq : q ∣ envelopingPrimeProduct w z) :
    (∑ d1 ∈ (envelopingPrimeProduct w z).divisors,
      ∑ d2 ∈ (envelopingPrimeProduct w z).divisors,
        (if q ∣ Nat.lcm d1 d2 then
          (ArithmeticFunction.moebius d1 : ℝ) * envelopingG w d1 z *
            ((ArithmeticFunction.moebius d2 : ℝ) * envelopingG w d2 z) *
            envelopingDensity w (Nat.lcm d1 d2 / q)
        else 0)) =
    ∑ u1 ∈ (envelopingPrimeProduct w z).primeFactors.powerset,
      ∑ u2 ∈ (envelopingPrimeProduct w z).primeFactors.powerset,
        (if ((∏ p ∈ u1, p : ℕ) : ℝ) ≤ z then envelopingH w (∏ p ∈ u1, p) else 0) *
          (if ((∏ p ∈ u2, p : ℕ) : ℝ) ≤ z then envelopingH w (∏ p ∈ u2, p) else 0) *
          ∏ p ∈ (envelopingPrimeProduct w z).primeFactors,
            ((if p ∈ u1 ∧ p ∈ u2 then
            (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
              ((envelopingOmega w p : ℝ) / p) ^ 2 else 0)
          + (if p ∈ u1 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∈ u2 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∣ q then (0 : ℝ) else 1)) := by
  rw [vdc_assemble hw hz hq]
  rw [sel_sum_divisors (vdc_P_sqfree hw z)]
  apply Finset.sum_congr rfl
  intro u1 hu1
  rw [sel_sum_divisors (vdc_P_sqfree hw z)]
  apply Finset.sum_congr rfl
  intro u2 hu2
  have hu1s : u1 ⊆ (envelopingPrimeProduct w z).primeFactors := Finset.mem_powerset.mp hu1
  have hu2s : u2 ⊆ (envelopingPrimeProduct w z).primeFactors := Finset.mem_powerset.mp hu2
  rw [vdc_psi_factor (w := w) (q := q) hw hq (vdc_E_mem hw hu1s) (vdc_E_mem hw hu2s),
    vdc_E_pf' hu1s, vdc_E_pf' hu2s]


/-- The weight of a divisor set as a product over the prime support. -/
private theorem vdc_W_eq {w : ℕ} (hw : 5 ≤ w) {z : ℝ} {u : Finset ℕ}
    (hu : u ⊆ (envelopingPrimeProduct w z).primeFactors) :
    (∏ p ∈ (envelopingPrimeProduct w z).primeFactors, (if p ∈ u then envelopingH w p else 1)) = envelopingH w (∏ p ∈ u, p) := by
  rw [(vdc_prod_ite_mem_single hu (fun p => envelopingH w p)).symm]
  have h1 : (∏ p ∈ u, envelopingH w p)
      = ∏ p ∈ u, (envelopingOmega w p : ℝ) / (p - envelopingOmega w p : ℕ) := by
    apply Finset.prod_congr rfl
    intro p hp
    rw [vdc_H_prime hw (hu hp)]
    have hwp : w < p := efs_prime_gt (vdc_prime (hu hp)) (Nat.dvd_of_mem_primeFactors (hu hp))
    have hom1 : 1 ≤ envelopingOmega w p := by
      unfold envelopingOmega
      rw [if_neg (by omega : ¬ p ≤ w)]
      split_ifs <;> omega
    have hom2 : envelopingOmega w p ≤ 2 := by
      unfold envelopingOmega
      rw [if_neg (by omega : ¬ p ≤ w)]
      split_ifs <;> omega
    have hle : envelopingOmega w p ≤ p := by omega
    have hp0 : (0 : ℝ) < p := by
      have : 0 < p := (vdc_prime (hu hp)).pos
      exact_mod_cast this
    rw [Nat.cast_sub hle]
    have h2 : (0 : ℝ) < (p : ℝ) - (envelopingOmega w p : ℝ) := by
      have h2a : (envelopingOmega w p : ℝ) ≤ 2 := by exact_mod_cast hom2
      have h2b : (6 : ℝ) ≤ p := by
        have : 6 ≤ p := by omega
        exact_mod_cast this
      linarith
    field_simp
  rw [h1, ← vdc_H_E hw hu]

/-- The product of the local weights over a subset of the support. -/
private theorem vdc_H_prod {w : ℕ} (hw : 5 ≤ w) {z : ℝ} {u : Finset ℕ}
    (hu : u ⊆ (envelopingPrimeProduct w z).primeFactors) :
    (∏ p ∈ u, envelopingH w p) = envelopingH w (∏ p ∈ u, p) := by
  rw [vdc_prod_ite_mem_single hu (fun p => envelopingH w p), vdc_W_eq hw hu]

/-- The `q`-part local factor is nonnegative. -/
private theorem vdc_qs_nn {w : ℕ} {z : ℝ} {p : ℕ} (hw : 5 ≤ w)
    (hp : p ∈ (envelopingPrimeProduct w z).primeFactors) :
    0 ≤ 2 / (1 - (envelopingOmega w p : ℝ) / p)
        + (1 - 2 * ((envelopingOmega w p : ℝ) / p)) / (1 - (envelopingOmega w p : ℝ) / p) ^ 2 := by
  have hwp : w < p := efs_prime_gt (vdc_prime hp) (Nat.dvd_of_mem_primeFactors hp)
  have hom1 : 1 ≤ envelopingOmega w p := by
    unfold envelopingOmega
    rw [if_neg (by omega : ¬ p ≤ w)]
    split_ifs <;> omega
  have hom2 : envelopingOmega w p ≤ 2 := by
    unfold envelopingOmega
    rw [if_neg (by omega : ¬ p ≤ w)]
    split_ifs <;> omega
  have hp0 : (0 : ℝ) < p := by
    have : 0 < p := (vdc_prime hp).pos
    exact_mod_cast this
  have hp6 : (6 : ℝ) ≤ p := by
    have : 6 ≤ p := by omega
    exact_mod_cast this
  have ha2 : (envelopingOmega w p : ℝ) ≤ 2 := by exact_mod_cast hom2
  set a : ℝ := (envelopingOmega w p : ℝ) / p with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  have halt : a ≤ 1 / 3 := by
    rw [ha, div_le_iff₀ hp0]
    linarith
  have h1a : 0 < 1 - a := by linarith
  have key : 2 / (1 - a) + (1 - 2 * a) / (1 - a) ^ 2 = (3 - 4 * a) / (1 - a) ^ 2 := by
    field_simp
    ring
  rw [key]
  apply div_nonneg _ (by positivity)
  linarith

/-- The local product over the support, evaluated on the `q`-free part and the `q`-part. -/
private theorem vdc_product_eval {w q : ℕ} (hw : 5 ≤ w) {z : ℝ}
    (hq : q ∣ envelopingPrimeProduct w z) {n1 n2 a1 a2 : Finset ℕ}
    (hn1 : n1 ⊆ (envelopingPrimeProduct w z).primeFactors.filter (fun p => ¬ p ∣ q)) (hn2 : n2 ⊆ (envelopingPrimeProduct w z).primeFactors.filter (fun p => ¬ p ∣ q))
    (ha1 : a1 ⊆ (envelopingPrimeProduct w z).primeFactors.filter (fun p => p ∣ q)) (ha2 : a2 ⊆ (envelopingPrimeProduct w z).primeFactors.filter (fun p => p ∣ q)) :
    (∏ p ∈ (envelopingPrimeProduct w z).primeFactors,
        (if p ∈ n1 ∪ a1 then envelopingH w p else 1) * (if p ∈ n2 ∪ a2 then envelopingH w p else 1) *
          |((if p ∈ n1 ∪ a1 ∧ p ∈ n2 ∪ a2 then
            (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
              ((envelopingOmega w p : ℝ) / p) ^ 2 else 0)
          + (if p ∈ n1 ∪ a1 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∈ n2 ∪ a2 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∣ q then (0 : ℝ) else 1))|)
      = (if n1 = n2 then ∏ p ∈ n1, envelopingH w p else 0) *
        ∏ p ∈ (envelopingPrimeProduct w z).primeFactors.filter (fun p => p ∣ q),
          (if p ∈ a1 ∧ p ∈ a2 then
            (1 - 2 * ((envelopingOmega w p : ℝ) / p)) / (1 - (envelopingOmega w p : ℝ) / p) ^ 2
            else if p ∈ a1 ∨ p ∈ a2 then 1 / (1 - (envelopingOmega w p : ℝ) / p) else 0) := by
  have hqsS : ((envelopingPrimeProduct w z).primeFactors.filter (fun p => p ∣ q)) ⊆ (envelopingPrimeProduct w z).primeFactors := Finset.filter_subset _ _
  have hunion : ((envelopingPrimeProduct w z).primeFactors.filter (fun p => ¬ p ∣ q)) ∪ ((envelopingPrimeProduct w z).primeFactors.filter (fun p => p ∣ q)) = (envelopingPrimeProduct w z).primeFactors := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    tauto
  have hdisj : Disjoint ((envelopingPrimeProduct w z).primeFactors.filter (fun p => ¬ p ∣ q))
      ((envelopingPrimeProduct w z).primeFactors.filter (fun p => p ∣ q)) := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    exact (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hp').2
  have hSdiff : (envelopingPrimeProduct w z).primeFactors \ ((envelopingPrimeProduct w z).primeFactors.filter (fun p => p ∣ q))
      = ((envelopingPrimeProduct w z).primeFactors.filter (fun p => ¬ p ∣ q)) := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_filter]
    tauto
  rw [vdc_prod_sdiff_split hqsS, hSdiff]
  congr 1
  · apply Eq.trans (b := ∏ p ∈ (envelopingPrimeProduct w z).primeFactors.filter (fun p => ¬ p ∣ q),
        (if p ∈ n1 ∧ p ∈ n2 then envelopingH w p else if p ∈ n1 ∨ p ∈ n2 then 0 else 1))
    · apply Finset.prod_congr rfl
      intro p hp
      have hpS : p ∈ (envelopingPrimeProduct w z).primeFactors := (Finset.mem_filter.mp hp).1
      have hpq : ¬ p ∣ q := (Finset.mem_filter.mp hp).2
      exact vdc_A_off (z := z) hw hpS hpq Finset.subset_union_left Finset.subset_union_left
        (fun x hx hx' => by
          rcases Finset.mem_union.mp hx with h | h
          · exact absurd h hx'
          · exact (Finset.mem_filter.mp (ha1 h)).2)
        (fun x hx hx' => by
          rcases Finset.mem_union.mp hx with h | h
          · exact absurd h hx'
          · exact (Finset.mem_filter.mp (ha2 h)).2)
    · rw [← hSdiff]
      exact vdc_off_prod (w := w) hunion hdisj hn1 hn2
  · apply Finset.prod_congr rfl
    intro p hp
    have hpS : p ∈ (envelopingPrimeProduct w z).primeFactors := (Finset.mem_filter.mp hp).1
    have hpq : p ∣ q := (Finset.mem_filter.mp hp).2
    exact vdc_A_qs (z := z) hw hpS hpq Finset.subset_union_right Finset.subset_union_right
      (fun x hx hx' => by
        rcases Finset.mem_union.mp hx with h | h
        · exact (Finset.mem_filter.mp (hn1 h)).2
        · exact absurd h hx')
      (fun x hx hx' => by
        rcases Finset.mem_union.mp hx with h | h
        · exact (Finset.mem_filter.mp (hn2 h)).2
        · exact absurd h hx')


/-- The mass of the `q`-free part of the support, with the Selberg cutoff, is at most `G 1`. -/
private theorem vdc_mass_off {w q : ℕ} (hw : 5 ≤ w) {z : ℝ} (hz : 1 ≤ z) :
    (∑ n ∈ ((envelopingPrimeProduct w z).primeFactors.filter (fun p => ¬ p ∣ q)).powerset,
        (if ((∏ p ∈ n, p : ℕ) : ℝ) ≤ z then ∏ p ∈ n, envelopingH w p else 0))
      ≤ envelopingG w 1 z := by
  have hsub : ((envelopingPrimeProduct w z).primeFactors.filter (fun p => ¬ p ∣ q)).powerset ⊆ ((envelopingPrimeProduct w z).primeFactors).powerset :=
    Finset.powerset_mono.mpr (Finset.filter_subset _ _)
  have hstep : (∑ n ∈ ((envelopingPrimeProduct w z).primeFactors.filter (fun p => ¬ p ∣ q)).powerset,
        (if ((∏ p ∈ n, p : ℕ) : ℝ) ≤ z then ∏ p ∈ n, envelopingH w p else 0))
      = ∑ n ∈ ((envelopingPrimeProduct w z).primeFactors.filter (fun p => ¬ p ∣ q)).powerset,
        (if ((∏ p ∈ n, p : ℕ) : ℝ) ≤ z then envelopingH w (∏ p ∈ n, p) else 0) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hnS : n ⊆ (envelopingPrimeProduct w z).primeFactors :=
      Finset.Subset.trans (Finset.mem_powerset.mp hn) (Finset.filter_subset _ _)
    by_cases h : ((∏ p ∈ n, p : ℕ) : ℝ) ≤ z
    · rw [if_pos h, if_pos h, vdc_H_prod hw hnS]
    · rw [if_neg h, if_neg h]
  rw [hstep]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_) (vdc_mass hw hz)
  intro n hn _
  split_ifs
  · exact vdc_H_nonneg w _
  · exact le_rfl

/-- The double sum of the `q`-part weights is at most `4` to the number of primes. -/
private theorem vdc_qs_sum_bound {w q : ℕ} (hw : 5 ≤ w) {z : ℝ} {qs : Finset ℕ}
    (hqs : qs ⊆ (envelopingPrimeProduct w z).primeFactors) :
    (∑ a1 ∈ qs.powerset, ∑ a2 ∈ qs.powerset,
      ∏ p ∈ qs, (if p ∈ a1 ∧ p ∈ a2 then
          (1 - 2 * ((envelopingOmega w p : ℝ) / p)) / (1 - (envelopingOmega w p : ℝ) / p) ^ 2
          else if p ∈ a1 ∨ p ∈ a2 then 1 / (1 - (envelopingOmega w p : ℝ) / p) else 0))
      ≤ 4 ^ qs.card := by
  have hpair := vdc_pair_prod qs (fun p (i : Bool) (j : Bool) =>
    if i then (if j then
      (1 - 2 * ((envelopingOmega w p : ℝ) / p)) / (1 - (envelopingOmega w p : ℝ) / p) ^ 2
      else 1 / (1 - (envelopingOmega w p : ℝ) / p))
    else (if j then 1 / (1 - (envelopingOmega w p : ℝ) / p) else 0))
  have hpair' : (∏ p ∈ qs, ((1 - 2 * ((envelopingOmega w p : ℝ) / p)) / (1 - (envelopingOmega w p : ℝ) / p) ^ 2
        + 1 / (1 - (envelopingOmega w p : ℝ) / p)
        + 1 / (1 - (envelopingOmega w p : ℝ) / p) + 0))
      = ∑ a1 ∈ qs.powerset, ∑ a2 ∈ qs.powerset,
      ∏ p ∈ qs, (if p ∈ a1 then (if p ∈ a2 then (1 - 2 * ((envelopingOmega w p : ℝ) / p)) / (1 - (envelopingOmega w p : ℝ) / p) ^ 2
          else 1 / (1 - (envelopingOmega w p : ℝ) / p)) else (if p ∈ a2 then 1 / (1 - (envelopingOmega w p : ℝ) / p) else 0)) := by
    simpa using hpair
  have hconv : (∑ a1 ∈ qs.powerset, ∑ a2 ∈ qs.powerset,
      ∏ p ∈ qs, (if p ∈ a1 then (if p ∈ a2 then (1 - 2 * ((envelopingOmega w p : ℝ) / p)) / (1 - (envelopingOmega w p : ℝ) / p) ^ 2
          else 1 / (1 - (envelopingOmega w p : ℝ) / p)) else (if p ∈ a2 then 1 / (1 - (envelopingOmega w p : ℝ) / p) else 0)))
      = ∑ a1 ∈ qs.powerset, ∑ a2 ∈ qs.powerset,
      ∏ p ∈ qs, (if p ∈ a1 ∧ p ∈ a2 then (1 - 2 * ((envelopingOmega w p : ℝ) / p)) / (1 - (envelopingOmega w p : ℝ) / p) ^ 2
          else if p ∈ a1 ∨ p ∈ a2 then 1 / (1 - (envelopingOmega w p : ℝ) / p) else 0) := by
    apply Finset.sum_congr rfl
    intro a1 _
    apply Finset.sum_congr rfl
    intro a2 _
    apply Finset.prod_congr rfl
    intro p _
    by_cases h1 : p ∈ a1 <;> by_cases h2 : p ∈ a2 <;> simp [h1, h2]
  rw [← hconv, ← hpair', ← Finset.prod_const (s := qs) (b := (4 : ℝ))]
  have hfac : ∀ p : ℕ, ((1 - 2 * ((envelopingOmega w p : ℝ) / p)) / (1 - (envelopingOmega w p : ℝ) / p) ^ 2
        + 1 / (1 - (envelopingOmega w p : ℝ) / p) + 1 / (1 - (envelopingOmega w p : ℝ) / p) + 0)
      = 2 / (1 - (envelopingOmega w p : ℝ) / p)
        + (1 - 2 * ((envelopingOmega w p : ℝ) / p)) / (1 - (envelopingOmega w p : ℝ) / p) ^ 2 := by
    intro p
    ring
  have h0 : ∀ p ∈ qs, 0 ≤ ((1 - 2 * ((envelopingOmega w p : ℝ) / p)) / (1 - (envelopingOmega w p : ℝ) / p) ^ 2
        + 1 / (1 - (envelopingOmega w p : ℝ) / p) + 1 / (1 - (envelopingOmega w p : ℝ) / p) + 0) := by
    intro p hp
    rw [hfac p]
    exact vdc_qs_nn hw (hqs hp)
  have h1 : ∀ p ∈ qs, ((1 - 2 * ((envelopingOmega w p : ℝ) / p)) / (1 - (envelopingOmega w p : ℝ) / p) ^ 2
        + 1 / (1 - (envelopingOmega w p : ℝ) / p) + 1 / (1 - (envelopingOmega w p : ℝ) / p) + 0) ≤ 4 := by
    intro p hp
    rw [hfac p]
    exact vdc_qs_arith (w := w) (z := z) hw (hqs hp)
  apply prod_le_prod₀
  · exact h0
  · exact h1


/-- The two nonnegative parts of the `q`-part local factor. -/
private theorem vdc_qs_pos {w : ℕ} {z : ℝ} {p : ℕ} (hw : 5 ≤ w)
    (hp : p ∈ (envelopingPrimeProduct w z).primeFactors) :
    0 ≤ (1 - 2 * ((envelopingOmega w p : ℝ) / p)) / (1 - (envelopingOmega w p : ℝ) / p) ^ 2
    ∧ 0 ≤ 1 / (1 - (envelopingOmega w p : ℝ) / p) := by
  have hwp : w < p := efs_prime_gt (vdc_prime hp) (Nat.dvd_of_mem_primeFactors hp)
  have hom1 : 1 ≤ envelopingOmega w p := by
    unfold envelopingOmega
    rw [if_neg (by omega : ¬ p ≤ w)]
    split_ifs <;> omega
  have hom2 : envelopingOmega w p ≤ 2 := by
    unfold envelopingOmega
    rw [if_neg (by omega : ¬ p ≤ w)]
    split_ifs <;> omega
  have hp0 : (0 : ℝ) < p := by
    have : 0 < p := (vdc_prime hp).pos
    exact_mod_cast this
  have ha2 : (envelopingOmega w p : ℝ) ≤ 2 := by exact_mod_cast hom2
  have hp6 : (6 : ℝ) ≤ p := by
    have : 6 ≤ p := by omega
    exact_mod_cast this
  set a : ℝ := (envelopingOmega w p : ℝ) / p with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  have halt : a ≤ 1 / 2 := by
    rw [ha, div_le_iff₀ hp0]
    linarith
  constructor
  · apply div_nonneg _ (by positivity)
    linarith
  · apply div_nonneg (by norm_num)
    linarith

/-- The `q`-part product is nonnegative. -/
private theorem vdc_qs_prod_nn {w q : ℕ} (hw : 5 ≤ w) {z : ℝ} {qs : Finset ℕ}
    (hqs : qs ⊆ (envelopingPrimeProduct w z).primeFactors) (a1 a2 : Finset ℕ) :
    0 ≤ ∏ p ∈ qs, (if p ∈ a1 ∧ p ∈ a2 then
            (1 - 2 * ((envelopingOmega w p : ℝ) / p)) / (1 - (envelopingOmega w p : ℝ) / p) ^ 2
            else if p ∈ a1 ∨ p ∈ a2 then 1 / (1 - (envelopingOmega w p : ℝ) / p) else 0) := by
  apply Finset.prod_nonneg
  intro p hp
  by_cases h1 : p ∈ a1 <;> by_cases h2 : p ∈ a2
  · simp only [h1, h2, if_true, and_self]
    exact (vdc_qs_pos hw (hqs hp)).1
  · simp only [h1, h2, if_true, if_false, and_false, or_false]
    exact (vdc_qs_pos hw (hqs hp)).2
  · simp only [h1, h2, if_true, if_false, and_false, or_false]
    exact (vdc_qs_pos hw (hqs hp)).2
  · simp only [h1, h2, if_false, and_false, or_self]
    exact le_rfl

/-- The twisted Selberg form is at most `G 1` times `4` to the number of primes of `q`. -/
private theorem vdc_core {w q : ℕ} (hw : 5 ≤ w) {z : ℝ} (hz : 1 ≤ z)
    (hq : q ∣ envelopingPrimeProduct w z) :
    |∑ d1 ∈ (envelopingPrimeProduct w z).divisors,
      ∑ d2 ∈ (envelopingPrimeProduct w z).divisors,
        (if q ∣ Nat.lcm d1 d2 then
          (ArithmeticFunction.moebius d1 : ℝ) * envelopingG w d1 z *
            ((ArithmeticFunction.moebius d2 : ℝ) * envelopingG w d2 z) *
            envelopingDensity w (Nat.lcm d1 d2 / q)
        else 0)| ≤ envelopingG w 1 z * 4 ^ q.primeFactors.card := by
  have hP0 : (envelopingPrimeProduct w z) ≠ 0 := envelopingPrimeProduct_ne_zero w z
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hP0 (Nat.zero_dvd.mp hq)
  have hEmono : ∀ n a : Finset ℕ, n ∪ a ⊆ (envelopingPrimeProduct w z).primeFactors →
      ((∏ p ∈ n, p : ℕ) : ℝ) ≤ ((∏ p ∈ n ∪ a, p : ℕ) : ℝ) := by
    intro n a hna
    have h1 : ∏ p ∈ n, p ≤ ∏ p ∈ n ∪ a, p :=
      Finset.prod_le_prod_of_subset_of_one_le Finset.subset_union_left
        (fun x hx _ => (vdc_prime (hna hx)).one_le)
    exact_mod_cast h1
  have hI2 : ∀ t : ℝ, (if t ≤ z then (1 : ℝ) else 0) ≤ 1 := by
    intro t
    split_ifs <;> norm_num
  have hI1 : ∀ n a : Finset ℕ, n ∪ a ⊆ (envelopingPrimeProduct w z).primeFactors →
      (if ((∏ p ∈ n ∪ a, p : ℕ) : ℝ) ≤ z then (1 : ℝ) else 0) ≤
        (if ((∏ p ∈ n, p : ℕ) : ℝ) ≤ z then (1 : ℝ) else 0) := by
    intro n a hna
    by_cases h : ((∏ p ∈ n, p : ℕ) : ℝ) ≤ z
    · rw [if_pos h]
      split_ifs <;> norm_num
    · rw [if_neg h, if_neg (fun hc => h (le_trans (hEmono n a hna) hc))]
  have hAform : ∀ u : Finset ℕ, u ⊆ (envelopingPrimeProduct w z).primeFactors → (if ((∏ p ∈ u, p : ℕ) : ℝ) ≤ z then envelopingH w (∏ p ∈ u, p) else 0) = (if ((∏ p ∈ u, p : ℕ) : ℝ) ≤ z then (1 : ℝ) else 0) * (∏ p ∈ (envelopingPrimeProduct w z).primeFactors, (if p ∈ u then envelopingH w p else 1)) := by
    intro u hu
    by_cases h : ((∏ p ∈ u, p : ℕ) : ℝ) ≤ z
    · rw [if_pos h, if_pos h, one_mul, vdc_W_eq hw hu]
    · rw [if_neg h, if_neg h, zero_mul]
  have hAnneg : ∀ u : Finset ℕ, 0 ≤ (if ((∏ p ∈ u, p : ℕ) : ℝ) ≤ z then envelopingH w (∏ p ∈ u, p) else 0) := by
    intro u
    split_ifs
    · exact vdc_H_nonneg w _
    · exact le_rfl
  have hTermEq : ∀ u1 : Finset ℕ, u1 ⊆ (envelopingPrimeProduct w z).primeFactors → ∀ u2 : Finset ℕ, u2 ⊆ (envelopingPrimeProduct w z).primeFactors →
      |(if ((∏ p ∈ u1, p : ℕ) : ℝ) ≤ z then envelopingH w (∏ p ∈ u1, p) else 0) * (if ((∏ p ∈ u2, p : ℕ) : ℝ) ≤ z then envelopingH w (∏ p ∈ u2, p) else 0) *
          ∏ p ∈ (envelopingPrimeProduct w z).primeFactors, ((if p ∈ u1 ∧ p ∈ u2 then
            (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
              ((envelopingOmega w p : ℝ) / p) ^ 2 else 0)
          + (if p ∈ u1 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∈ u2 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∣ q then (0 : ℝ) else 1))| = (if ((∏ p ∈ u1, p : ℕ) : ℝ) ≤ z then (1 : ℝ) else 0) * (if ((∏ p ∈ u2, p : ℕ) : ℝ) ≤ z then (1 : ℝ) else 0) * ∏ p ∈ (envelopingPrimeProduct w z).primeFactors, (if p ∈ u1 then envelopingH w p else 1) * (if p ∈ u2 then envelopingH w p else 1) *
          |((if p ∈ u1 ∧ p ∈ u2 then
            (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
              ((envelopingOmega w p : ℝ) / p) ^ 2 else 0)
          + (if p ∈ u1 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∈ u2 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∣ q then (0 : ℝ) else 1))| := by
    intro u1 hu1 u2 hu2
    rw [abs_mul, abs_mul, abs_of_nonneg (hAnneg u1), abs_of_nonneg (hAnneg u2),
      Finset.abs_prod, hAform u1 hu1, hAform u2 hu2]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    ring
  have hbound : ∀ n1 : Finset ℕ, n1 ⊆ (envelopingPrimeProduct w z).primeFactors.filter (fun p => ¬ p ∣ q) → ∀ n2 : Finset ℕ, n2 ⊆ (envelopingPrimeProduct w z).primeFactors.filter (fun p => ¬ p ∣ q) →
      ∀ a1 : Finset ℕ, a1 ⊆ (envelopingPrimeProduct w z).primeFactors.filter (fun p => p ∣ q) → ∀ a2 : Finset ℕ, a2 ⊆ (envelopingPrimeProduct w z).primeFactors.filter (fun p => p ∣ q) →
      (if ((∏ p ∈ n1 ∪ a1, p : ℕ) : ℝ) ≤ z then (1 : ℝ) else 0) * (if ((∏ p ∈ n2 ∪ a2, p : ℕ) : ℝ) ≤ z then (1 : ℝ) else 0) * ∏ p ∈ (envelopingPrimeProduct w z).primeFactors, (if p ∈ n1 ∪ a1 then envelopingH w p else 1) * (if p ∈ n2 ∪ a2 then envelopingH w p else 1) *
          |((if p ∈ n1 ∪ a1 ∧ p ∈ n2 ∪ a2 then
            (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
              ((envelopingOmega w p : ℝ) / p) ^ 2 else 0)
          + (if p ∈ n1 ∪ a1 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∈ n2 ∪ a2 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∣ q then (0 : ℝ) else 1))|
        ≤ (if n1 = n2 then (if ((∏ p ∈ n1, p : ℕ) : ℝ) ≤ z then ∏ p ∈ n1, envelopingH w p else 0) else 0) * ∏ p ∈ (envelopingPrimeProduct w z).primeFactors.filter (fun p => p ∣ q), (if p ∈ a1 ∧ p ∈ a2 then
            (1 - 2 * ((envelopingOmega w p : ℝ) / p)) / (1 - (envelopingOmega w p : ℝ) / p) ^ 2
            else if p ∈ a1 ∨ p ∈ a2 then 1 / (1 - (envelopingOmega w p : ℝ) / p) else 0) := by
    intro n1 hn1 n2 hn2 a1 ha1 a2 ha2
    rw [vdc_product_eval (w := w) (q := q) hw (z := z) hq hn1 hn2 ha1 ha2]
    have hQFnn : (0 : ℝ) ≤ ∏ p ∈ (envelopingPrimeProduct w z).primeFactors.filter (fun p => p ∣ q), (if p ∈ a1 ∧ p ∈ a2 then
            (1 - 2 * ((envelopingOmega w p : ℝ) / p)) / (1 - (envelopingOmega w p : ℝ) / p) ^ 2
            else if p ∈ a1 ∨ p ∈ a2 then 1 / (1 - (envelopingOmega w p : ℝ) / p) else 0) := vdc_qs_prod_nn (q := q) hw (Finset.filter_subset _ _) a1 a2
    have hPnn : (0 : ℝ) ≤ ∏ p ∈ n1, envelopingH w p :=
      Finset.prod_nonneg (fun p _ => vdc_H_nonneg w p)
    by_cases hnn : n1 = n2
    · subst hnn
      rw [if_pos rfl, if_pos rfl]
      by_cases hEz : ((∏ p ∈ n1, p : ℕ) : ℝ) ≤ z
      · rw [if_pos hEz]
        have hIle : (if ((∏ p ∈ n1 ∪ a1, p : ℕ) : ℝ) ≤ z then (1 : ℝ) else 0) * (if ((∏ p ∈ n1 ∪ a2, p : ℕ) : ℝ) ≤ z then (1 : ℝ) else 0) ≤ 1 := by
          split_ifs <;> norm_num
        calc (if ((∏ p ∈ n1 ∪ a1, p : ℕ) : ℝ) ≤ z then (1 : ℝ) else 0) * (if ((∏ p ∈ n1 ∪ a2, p : ℕ) : ℝ) ≤ z then (1 : ℝ) else 0) *
              ((∏ p ∈ n1, envelopingH w p) * ∏ p ∈ (envelopingPrimeProduct w z).primeFactors.filter (fun p => p ∣ q), (if p ∈ a1 ∧ p ∈ a2 then
            (1 - 2 * ((envelopingOmega w p : ℝ) / p)) / (1 - (envelopingOmega w p : ℝ) / p) ^ 2
            else if p ∈ a1 ∨ p ∈ a2 then 1 / (1 - (envelopingOmega w p : ℝ) / p) else 0))
            = ((if ((∏ p ∈ n1 ∪ a1, p : ℕ) : ℝ) ≤ z then (1 : ℝ) else 0) * (if ((∏ p ∈ n1 ∪ a2, p : ℕ) : ℝ) ≤ z then (1 : ℝ) else 0)) *
              ((∏ p ∈ n1, envelopingH w p) * ∏ p ∈ (envelopingPrimeProduct w z).primeFactors.filter (fun p => p ∣ q), (if p ∈ a1 ∧ p ∈ a2 then
            (1 - 2 * ((envelopingOmega w p : ℝ) / p)) / (1 - (envelopingOmega w p : ℝ) / p) ^ 2
            else if p ∈ a1 ∨ p ∈ a2 then 1 / (1 - (envelopingOmega w p : ℝ) / p) else 0)) := by ring
          _ ≤ 1 * ((∏ p ∈ n1, envelopingH w p) * ∏ p ∈ (envelopingPrimeProduct w z).primeFactors.filter (fun p => p ∣ q), (if p ∈ a1 ∧ p ∈ a2 then
            (1 - 2 * ((envelopingOmega w p : ℝ) / p)) / (1 - (envelopingOmega w p : ℝ) / p) ^ 2
            else if p ∈ a1 ∨ p ∈ a2 then 1 / (1 - (envelopingOmega w p : ℝ) / p) else 0)) :=
              mul_le_mul_of_nonneg_right hIle (mul_nonneg hPnn hQFnn)
          _ = (∏ p ∈ n1, envelopingH w p) * ∏ p ∈ (envelopingPrimeProduct w z).primeFactors.filter (fun p => p ∣ q), (if p ∈ a1 ∧ p ∈ a2 then
            (1 - 2 * ((envelopingOmega w p : ℝ) / p)) / (1 - (envelopingOmega w p : ℝ) / p) ^ 2
            else if p ∈ a1 ∨ p ∈ a2 then 1 / (1 - (envelopingOmega w p : ℝ) / p) else 0) := by ring
      · rw [if_neg hEz]
        have h0 : (if ((∏ p ∈ n1 ∪ a1, p : ℕ) : ℝ) ≤ z then (1 : ℝ) else 0) = 0 := by
          rw [if_neg (fun hc => hEz (le_trans (hEmono n1 a1 (Finset.union_subset
            (Finset.Subset.trans hn1 (Finset.filter_subset _ _))
            (Finset.Subset.trans ha1 (Finset.filter_subset _ _)))) hc))]
        rw [h0]
        norm_num
    · rw [if_neg hnn, if_neg hnn]
      norm_num
  have hmain : |∑ d1 ∈ (envelopingPrimeProduct w z).divisors,
      ∑ d2 ∈ (envelopingPrimeProduct w z).divisors,
        (if q ∣ Nat.lcm d1 d2 then
          (ArithmeticFunction.moebius d1 : ℝ) * envelopingG w d1 z *
            ((ArithmeticFunction.moebius d2 : ℝ) * envelopingG w d2 z) *
            envelopingDensity w (Nat.lcm d1 d2 / q)
        else 0)| ≤ ∑ u1 ∈ ((envelopingPrimeProduct w z).primeFactors).powerset, ∑ u2 ∈ ((envelopingPrimeProduct w z).primeFactors).powerset, |(if ((∏ p ∈ u1, p : ℕ) : ℝ) ≤ z then envelopingH w (∏ p ∈ u1, p) else 0) * (if ((∏ p ∈ u2, p : ℕ) : ℝ) ≤ z then envelopingH w (∏ p ∈ u2, p) else 0) *
          ∏ p ∈ (envelopingPrimeProduct w z).primeFactors, ((if p ∈ u1 ∧ p ∈ u2 then
            (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
              ((envelopingOmega w p : ℝ) / p) ^ 2 else 0)
          + (if p ∈ u1 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∈ u2 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∣ q then (0 : ℝ) else 1))| := by
    rw [vdc_subset_form (q := q) hw hz hq]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    apply Finset.sum_le_sum
    intro u1 _
    exact Finset.abs_sum_le_sum_abs _ _
  refine hmain.trans ?_
  have hstep1 : (∑ u1 ∈ ((envelopingPrimeProduct w z).primeFactors).powerset, ∑ u2 ∈ ((envelopingPrimeProduct w z).primeFactors).powerset, |(if ((∏ p ∈ u1, p : ℕ) : ℝ) ≤ z then envelopingH w (∏ p ∈ u1, p) else 0) * (if ((∏ p ∈ u2, p : ℕ) : ℝ) ≤ z then envelopingH w (∏ p ∈ u2, p) else 0) *
          ∏ p ∈ (envelopingPrimeProduct w z).primeFactors, ((if p ∈ u1 ∧ p ∈ u2 then
            (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
              ((envelopingOmega w p : ℝ) / p) ^ 2 else 0)
          + (if p ∈ u1 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∈ u2 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∣ q then (0 : ℝ) else 1))|)
      = ∑ u1 ∈ ((envelopingPrimeProduct w z).primeFactors).powerset, ∑ u2 ∈ ((envelopingPrimeProduct w z).primeFactors).powerset, (if ((∏ p ∈ u1, p : ℕ) : ℝ) ≤ z then (1 : ℝ) else 0) * (if ((∏ p ∈ u2, p : ℕ) : ℝ) ≤ z then (1 : ℝ) else 0) * ∏ p ∈ (envelopingPrimeProduct w z).primeFactors, (if p ∈ u1 then envelopingH w p else 1) * (if p ∈ u2 then envelopingH w p else 1) *
          |((if p ∈ u1 ∧ p ∈ u2 then
            (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
              ((envelopingOmega w p : ℝ) / p) ^ 2 else 0)
          + (if p ∈ u1 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∈ u2 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∣ q then (0 : ℝ) else 1))| := by
    apply Finset.sum_congr rfl
    intro u1 hu1
    apply Finset.sum_congr rfl
    intro u2 hu2
    exact hTermEq u1 (Finset.mem_powerset.mp hu1) u2 (Finset.mem_powerset.mp hu2)
  rw [hstep1]
  have hunion : ((envelopingPrimeProduct w z).primeFactors.filter (fun p => ¬ p ∣ q)) ∪ ((envelopingPrimeProduct w z).primeFactors.filter (fun p => p ∣ q)) = ((envelopingPrimeProduct w z).primeFactors) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    tauto
  have hdisj : Disjoint ((envelopingPrimeProduct w z).primeFactors.filter (fun p => ¬ p ∣ q)) ((envelopingPrimeProduct w z).primeFactors.filter (fun p => p ∣ q)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hx').2
  have hsplitA : (∑ u1 ∈ ((envelopingPrimeProduct w z).primeFactors).powerset, ∑ u2 ∈ ((envelopingPrimeProduct w z).primeFactors).powerset, (if ((∏ p ∈ u1, p : ℕ) : ℝ) ≤ z then (1 : ℝ) else 0) * (if ((∏ p ∈ u2, p : ℕ) : ℝ) ≤ z then (1 : ℝ) else 0) * ∏ p ∈ (envelopingPrimeProduct w z).primeFactors, (if p ∈ u1 then envelopingH w p else 1) * (if p ∈ u2 then envelopingH w p else 1) *
          |((if p ∈ u1 ∧ p ∈ u2 then
            (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
              ((envelopingOmega w p : ℝ) / p) ^ 2 else 0)
          + (if p ∈ u1 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∈ u2 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∣ q then (0 : ℝ) else 1))|)
      = ∑ n1 ∈ ((envelopingPrimeProduct w z).primeFactors.filter (fun p => ¬ p ∣ q)).powerset, ∑ a1 ∈ ((envelopingPrimeProduct w z).primeFactors.filter (fun p => p ∣ q)).powerset, ∑ u2 ∈ ((envelopingPrimeProduct w z).primeFactors).powerset, (if ((∏ p ∈ n1 ∪ a1, p : ℕ) : ℝ) ≤ z then (1 : ℝ) else 0) * (if ((∏ p ∈ u2, p : ℕ) : ℝ) ≤ z then (1 : ℝ) else 0) * ∏ p ∈ (envelopingPrimeProduct w z).primeFactors, (if p ∈ n1 ∪ a1 then envelopingH w p else 1) * (if p ∈ u2 then envelopingH w p else 1) *
          |((if p ∈ n1 ∪ a1 ∧ p ∈ u2 then
            (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
              ((envelopingOmega w p : ℝ) / p) ^ 2 else 0)
          + (if p ∈ n1 ∪ a1 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∈ u2 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∣ q then (0 : ℝ) else 1))| :=
    vdc_sum_powerset_split (s := (envelopingPrimeProduct w z).primeFactors) (off := (envelopingPrimeProduct w z).primeFactors.filter (fun p => ¬ p ∣ q)) (qs := (envelopingPrimeProduct w z).primeFactors.filter (fun p => p ∣ q)) hunion hdisj
      (fun u1 => ∑ u2 ∈ ((envelopingPrimeProduct w z).primeFactors).powerset, (if ((∏ p ∈ u1, p : ℕ) : ℝ) ≤ z then (1 : ℝ) else 0) * (if ((∏ p ∈ u2, p : ℕ) : ℝ) ≤ z then (1 : ℝ) else 0) * ∏ p ∈ (envelopingPrimeProduct w z).primeFactors, (if p ∈ u1 then envelopingH w p else 1) * (if p ∈ u2 then envelopingH w p else 1) *
          |((if p ∈ u1 ∧ p ∈ u2 then
            (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
              ((envelopingOmega w p : ℝ) / p) ^ 2 else 0)
          + (if p ∈ u1 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∈ u2 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∣ q then (0 : ℝ) else 1))|)
  rw [hsplitA]
  have hsplitB : ∀ n1 a1 : Finset ℕ, (∑ u2 ∈ ((envelopingPrimeProduct w z).primeFactors).powerset, (if ((∏ p ∈ n1 ∪ a1, p : ℕ) : ℝ) ≤ z then (1 : ℝ) else 0) * (if ((∏ p ∈ u2, p : ℕ) : ℝ) ≤ z then (1 : ℝ) else 0) * ∏ p ∈ (envelopingPrimeProduct w z).primeFactors, (if p ∈ n1 ∪ a1 then envelopingH w p else 1) * (if p ∈ u2 then envelopingH w p else 1) *
          |((if p ∈ n1 ∪ a1 ∧ p ∈ u2 then
            (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
              ((envelopingOmega w p : ℝ) / p) ^ 2 else 0)
          + (if p ∈ n1 ∪ a1 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∈ u2 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∣ q then (0 : ℝ) else 1))|)
      = ∑ n2 ∈ ((envelopingPrimeProduct w z).primeFactors.filter (fun p => ¬ p ∣ q)).powerset, ∑ a2 ∈ ((envelopingPrimeProduct w z).primeFactors.filter (fun p => p ∣ q)).powerset, (if ((∏ p ∈ n1 ∪ a1, p : ℕ) : ℝ) ≤ z then (1 : ℝ) else 0) * (if ((∏ p ∈ n2 ∪ a2, p : ℕ) : ℝ) ≤ z then (1 : ℝ) else 0) * ∏ p ∈ (envelopingPrimeProduct w z).primeFactors, (if p ∈ n1 ∪ a1 then envelopingH w p else 1) * (if p ∈ n2 ∪ a2 then envelopingH w p else 1) *
          |((if p ∈ n1 ∪ a1 ∧ p ∈ n2 ∪ a2 then
            (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
              ((envelopingOmega w p : ℝ) / p) ^ 2 else 0)
          + (if p ∈ n1 ∪ a1 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∈ n2 ∪ a2 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∣ q then (0 : ℝ) else 1))| := by
    intro n1 a1
    exact vdc_sum_powerset_split (s := (envelopingPrimeProduct w z).primeFactors) (off := (envelopingPrimeProduct w z).primeFactors.filter (fun p => ¬ p ∣ q)) (qs := (envelopingPrimeProduct w z).primeFactors.filter (fun p => p ∣ q)) hunion hdisj
      (fun u2 => (if ((∏ p ∈ n1 ∪ a1, p : ℕ) : ℝ) ≤ z then (1 : ℝ) else 0) * (if ((∏ p ∈ u2, p : ℕ) : ℝ) ≤ z then (1 : ℝ) else 0) * ∏ p ∈ (envelopingPrimeProduct w z).primeFactors, (if p ∈ n1 ∪ a1 then envelopingH w p else 1) * (if p ∈ u2 then envelopingH w p else 1) *
          |((if p ∈ n1 ∪ a1 ∧ p ∈ u2 then
            (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
              ((envelopingOmega w p : ℝ) / p) ^ 2 else 0)
          + (if p ∈ n1 ∪ a1 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∈ u2 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∣ q then (0 : ℝ) else 1))|)
  have hstep2 : (∑ n1 ∈ ((envelopingPrimeProduct w z).primeFactors.filter (fun p => ¬ p ∣ q)).powerset, ∑ a1 ∈ ((envelopingPrimeProduct w z).primeFactors.filter (fun p => p ∣ q)).powerset, ∑ u2 ∈ ((envelopingPrimeProduct w z).primeFactors).powerset, (if ((∏ p ∈ n1 ∪ a1, p : ℕ) : ℝ) ≤ z then (1 : ℝ) else 0) * (if ((∏ p ∈ u2, p : ℕ) : ℝ) ≤ z then (1 : ℝ) else 0) * ∏ p ∈ (envelopingPrimeProduct w z).primeFactors, (if p ∈ n1 ∪ a1 then envelopingH w p else 1) * (if p ∈ u2 then envelopingH w p else 1) *
          |((if p ∈ n1 ∪ a1 ∧ p ∈ u2 then
            (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
              ((envelopingOmega w p : ℝ) / p) ^ 2 else 0)
          + (if p ∈ n1 ∪ a1 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∈ u2 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∣ q then (0 : ℝ) else 1))|)
      = ∑ n1 ∈ ((envelopingPrimeProduct w z).primeFactors.filter (fun p => ¬ p ∣ q)).powerset, ∑ a1 ∈ ((envelopingPrimeProduct w z).primeFactors.filter (fun p => p ∣ q)).powerset, ∑ n2 ∈ ((envelopingPrimeProduct w z).primeFactors.filter (fun p => ¬ p ∣ q)).powerset, ∑ a2 ∈ ((envelopingPrimeProduct w z).primeFactors.filter (fun p => p ∣ q)).powerset, (if ((∏ p ∈ n1 ∪ a1, p : ℕ) : ℝ) ≤ z then (1 : ℝ) else 0) * (if ((∏ p ∈ n2 ∪ a2, p : ℕ) : ℝ) ≤ z then (1 : ℝ) else 0) * ∏ p ∈ (envelopingPrimeProduct w z).primeFactors, (if p ∈ n1 ∪ a1 then envelopingH w p else 1) * (if p ∈ n2 ∪ a2 then envelopingH w p else 1) *
          |((if p ∈ n1 ∪ a1 ∧ p ∈ n2 ∪ a2 then
            (if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
              ((envelopingOmega w p : ℝ) / p) ^ 2 else 0)
          + (if p ∈ n1 ∪ a1 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∈ n2 ∪ a2 then
              -((if p ∣ q then (1 : ℝ) else (envelopingOmega w p : ℝ) / p) /
                ((envelopingOmega w p : ℝ) / p)) else 0)
          + (if p ∣ q then (0 : ℝ) else 1))| := by
    apply Finset.sum_congr rfl
    intro n1 _
    apply Finset.sum_congr rfl
    intro a1 _
    exact hsplitB n1 a1
  rw [hstep2]
  refine le_trans (Finset.sum_le_sum (fun n1 hn1 => Finset.sum_le_sum (fun a1 ha1 =>
      Finset.sum_le_sum (fun n2 hn2 => Finset.sum_le_sum (fun a2 ha2 =>
        hbound n1 (Finset.mem_powerset.mp hn1) n2 (Finset.mem_powerset.mp hn2)
          a1 (Finset.mem_powerset.mp ha1) a2 (Finset.mem_powerset.mp ha2)))))) ?_
  have hfac : (∑ n1 ∈ ((envelopingPrimeProduct w z).primeFactors.filter (fun p => ¬ p ∣ q)).powerset, ∑ a1 ∈ ((envelopingPrimeProduct w z).primeFactors.filter (fun p => p ∣ q)).powerset, ∑ n2 ∈ ((envelopingPrimeProduct w z).primeFactors.filter (fun p => ¬ p ∣ q)).powerset, ∑ a2 ∈ ((envelopingPrimeProduct w z).primeFactors.filter (fun p => p ∣ q)).powerset,
        (if n1 = n2 then (if ((∏ p ∈ n1, p : ℕ) : ℝ) ≤ z then ∏ p ∈ n1, envelopingH w p else 0) else 0) * ∏ p ∈ (envelopingPrimeProduct w z).primeFactors.filter (fun p => p ∣ q), (if p ∈ a1 ∧ p ∈ a2 then
            (1 - 2 * ((envelopingOmega w p : ℝ) / p)) / (1 - (envelopingOmega w p : ℝ) / p) ^ 2
            else if p ∈ a1 ∨ p ∈ a2 then 1 / (1 - (envelopingOmega w p : ℝ) / p) else 0))
      = (∑ n1 ∈ ((envelopingPrimeProduct w z).primeFactors.filter (fun p => ¬ p ∣ q)).powerset, ∑ n2 ∈ ((envelopingPrimeProduct w z).primeFactors.filter (fun p => ¬ p ∣ q)).powerset, (if n1 = n2 then (if ((∏ p ∈ n1, p : ℕ) : ℝ) ≤ z then ∏ p ∈ n1, envelopingH w p else 0) else 0)) * (∑ a1 ∈ ((envelopingPrimeProduct w z).primeFactors.filter (fun p => p ∣ q)).powerset, ∑ a2 ∈ ((envelopingPrimeProduct w z).primeFactors.filter (fun p => p ∣ q)).powerset, ∏ p ∈ (envelopingPrimeProduct w z).primeFactors.filter (fun p => p ∣ q), (if p ∈ a1 ∧ p ∈ a2 then
            (1 - 2 * ((envelopingOmega w p : ℝ) / p)) / (1 - (envelopingOmega w p : ℝ) / p) ^ 2
            else if p ∈ a1 ∨ p ∈ a2 then 1 / (1 - (envelopingOmega w p : ℝ) / p) else 0)) := by
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro n1 _
    apply Finset.sum_congr rfl
    intro a1 _
    rw [Finset.sum_mul_sum]
  rw [hfac]
  have hmass : (∑ n1 ∈ ((envelopingPrimeProduct w z).primeFactors.filter (fun p => ¬ p ∣ q)).powerset, ∑ n2 ∈ ((envelopingPrimeProduct w z).primeFactors.filter (fun p => ¬ p ∣ q)).powerset, (if n1 = n2 then (if ((∏ p ∈ n1, p : ℕ) : ℝ) ≤ z then ∏ p ∈ n1, envelopingH w p else 0) else 0)) ≤ envelopingG w 1 z := by
    have hinner : ∀ n1 ∈ ((envelopingPrimeProduct w z).primeFactors.filter (fun p => ¬ p ∣ q)).powerset,
        (∑ n2 ∈ ((envelopingPrimeProduct w z).primeFactors.filter (fun p => ¬ p ∣ q)).powerset, (if n1 = n2 then (if ((∏ p ∈ n1, p : ℕ) : ℝ) ≤ z then ∏ p ∈ n1, envelopingH w p else 0) else 0))
        = (if ((∏ p ∈ n1, p : ℕ) : ℝ) ≤ z then ∏ p ∈ n1, envelopingH w p else 0) := by
      intro n1 hn1
      rw [Finset.sum_ite_eq, if_pos hn1]
    have hstep : (∑ n1 ∈ ((envelopingPrimeProduct w z).primeFactors.filter (fun p => ¬ p ∣ q)).powerset, ∑ n2 ∈ ((envelopingPrimeProduct w z).primeFactors.filter (fun p => ¬ p ∣ q)).powerset, (if n1 = n2 then (if ((∏ p ∈ n1, p : ℕ) : ℝ) ≤ z then ∏ p ∈ n1, envelopingH w p else 0) else 0))
        = ∑ n1 ∈ ((envelopingPrimeProduct w z).primeFactors.filter (fun p => ¬ p ∣ q)).powerset,
          (if ((∏ p ∈ n1, p : ℕ) : ℝ) ≤ z then ∏ p ∈ n1, envelopingH w p else 0) :=
      Finset.sum_congr rfl (fun n1 hn1 => hinner n1 hn1)
    rw [hstep]
    exact vdc_mass_off (q := q) hw hz
  have hqs : (∑ a1 ∈ ((envelopingPrimeProduct w z).primeFactors.filter (fun p => p ∣ q)).powerset, ∑ a2 ∈ ((envelopingPrimeProduct w z).primeFactors.filter (fun p => p ∣ q)).powerset, ∏ p ∈ (envelopingPrimeProduct w z).primeFactors.filter (fun p => p ∣ q), (if p ∈ a1 ∧ p ∈ a2 then
            (1 - 2 * ((envelopingOmega w p : ℝ) / p)) / (1 - (envelopingOmega w p : ℝ) / p) ^ 2
            else if p ∈ a1 ∨ p ∈ a2 then 1 / (1 - (envelopingOmega w p : ℝ) / p) else 0)) ≤ 4 ^ ((envelopingPrimeProduct w z).primeFactors.filter (fun p => p ∣ q)).card :=
    vdc_qs_sum_bound (w := w) (q := q) (z := z) hw (Finset.filter_subset _ _)
  have hqsn : (0 : ℝ) ≤ ∑ a1 ∈ ((envelopingPrimeProduct w z).primeFactors.filter (fun p => p ∣ q)).powerset, ∑ a2 ∈ ((envelopingPrimeProduct w z).primeFactors.filter (fun p => p ∣ q)).powerset, ∏ p ∈ (envelopingPrimeProduct w z).primeFactors.filter (fun p => p ∣ q), (if p ∈ a1 ∧ p ∈ a2 then
            (1 - 2 * ((envelopingOmega w p : ℝ) / p)) / (1 - (envelopingOmega w p : ℝ) / p) ^ 2
            else if p ∈ a1 ∨ p ∈ a2 then 1 / (1 - (envelopingOmega w p : ℝ) / p) else 0) :=
    Finset.sum_nonneg (fun a1 _ => Finset.sum_nonneg (fun a2 _ =>
      vdc_qs_prod_nn (q := q) hw (Finset.filter_subset _ _) a1 a2))
  have hG1n : (0 : ℝ) ≤ envelopingG w 1 z := (vdc_G1_pos hw hz).le
  refine (mul_le_mul hmass hqs hqsn hG1n).trans (le_of_eq ?_)
  have hqscard : ((envelopingPrimeProduct w z).primeFactors.filter (fun p => p ∣ q)).card = q.primeFactors.card := by
    congr 1
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hx, hxq⟩
      exact Nat.mem_primeFactors.mpr ⟨vdc_prime hx, hxq, hq0⟩
    · intro hx
      obtain ⟨hxp, hxq, -⟩ := Nat.mem_primeFactors.mp hx
      exact ⟨Nat.mem_primeFactors.mpr ⟨hxp, hxq.trans hq, hP0⟩, hxq⟩
  rw [hqscard]

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
  refine ⟨4, by norm_num, ?_⟩
  intro w hwBig z hz q hq
  have hwBig5 : (5 : ℝ) ≤ wBig := by
    calc (5 : ℝ) ≤ 10 := by norm_num
      _ = (10 : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ wBig := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (Real.one_le_rpow (by norm_num) (by positivity))
  have hw5 : 5 ≤ w := by exact_mod_cast (hwBig5.trans hwBig)
  have hG1 : 0 < envelopingG w 1 z := vdc_G1_pos hw5 hz
  have hne : envelopingG w 1 z ≠ 0 := hG1.ne'
  have hsum : (∑ d1 ∈ (envelopingPrimeProduct w z).divisors,
        ∑ d2 ∈ (envelopingPrimeProduct w z).divisors,
          (if q ∣ Nat.lcm d1 d2 then
            envelopingRho w d1 z * envelopingRho w d2 z *
              envelopingDensity w (Nat.lcm d1 d2 / q)
          else 0))
      = (1 / (envelopingG w 1 z) ^ 2) *
        (∑ d1 ∈ (envelopingPrimeProduct w z).divisors,
          ∑ d2 ∈ (envelopingPrimeProduct w z).divisors,
            (if q ∣ Nat.lcm d1 d2 then
              (ArithmeticFunction.moebius d1 : ℝ) * envelopingG w d1 z *
                ((ArithmeticFunction.moebius d2 : ℝ) * envelopingG w d2 z) *
                envelopingDensity w (Nat.lcm d1 d2 / q)
            else 0)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d1 _
    apply Finset.sum_congr rfl
    intro d2 _
    by_cases h : q ∣ Nat.lcm d1 d2
    · rw [if_pos h, if_pos h, vdc_rho_mul hne]
      ring
    · rw [if_neg h, if_neg h, mul_zero]
  rw [hsum]
  have hkey : envelopingG w 1 z * ((1 / (envelopingG w 1 z) ^ 2) *
        (∑ d1 ∈ (envelopingPrimeProduct w z).divisors,
          ∑ d2 ∈ (envelopingPrimeProduct w z).divisors,
            (if q ∣ Nat.lcm d1 d2 then
              (ArithmeticFunction.moebius d1 : ℝ) * envelopingG w d1 z *
                ((ArithmeticFunction.moebius d2 : ℝ) * envelopingG w d2 z) *
                envelopingDensity w (Nat.lcm d1 d2 / q)
            else 0)))
      = (∑ d1 ∈ (envelopingPrimeProduct w z).divisors,
          ∑ d2 ∈ (envelopingPrimeProduct w z).divisors,
            (if q ∣ Nat.lcm d1 d2 then
              (ArithmeticFunction.moebius d1 : ℝ) * envelopingG w d1 z *
                ((ArithmeticFunction.moebius d2 : ℝ) * envelopingG w d2 z) *
                envelopingDensity w (Nat.lcm d1 d2 / q)
            else 0)) / envelopingG w 1 z := by
    field_simp
  rw [hkey, abs_div, abs_of_pos hG1, div_le_iff₀ hG1]
  refine (vdc_core (q := q) hw5 hz hq).trans (le_of_eq ?_)
  ring

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
