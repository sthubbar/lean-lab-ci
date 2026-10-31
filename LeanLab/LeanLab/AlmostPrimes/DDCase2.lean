/-
AI-written Lean code, Claude, 2026-10-21, run PC 20261020T2303Z-14596, unit U-1296.
P0048 A. Dudek, L. Dunn, arXiv 2602.22720, Section 2, Lemma 2.1, Case 2, `3 ≤ w ≤ 285`, `z ≥ 286`.

The paper's own Case 2, read again on arxiv.org/html/2602.22720 this run: the product is split at
286, the part `286 ≤ p < z` is "bounded using Case 1", which rests on Rosser-Schoenfeld, and the
finite part is checked by computer, giving `K ≤ 1.86`. So Case 2 itself uses Rosser-Schoenfeld
for its tail; here that input stays the cited `RSHyp`, nothing new is assumed.

Proof. `∏_{w ≤ p < z} = A · B` with `A = ∏_{w ≤ p < 286}`, `B = ∏_{286 ≤ p < z}`.
`B ≤ 1.24 (log z / log 286)²` by `DDLemma21.lemma2_1_case1` ON `RSHyp`, and `B = 1` at `z = 286`.
If `A` is empty, `w = 284, 285`, then `1.24 log² w ≤ 1.86 log² 286`. Otherwise let `p` be the
least prime `≥ w`; `A ≤ H(p) = ∏_{p ≤ r ≤ 283} r/(r - 2)` and `log w ≤ log p`, so it suffices that
`1.24 H(p) log² p ≤ 1.86 log² 286` for the 60 odd primes `p < 286`. With `p^1024 ≤ 2^{u_p}` and
`2^8355 ≤ 286^1024` this is `124 · num · u_p² ≤ 186 · 8355² · den`, checked by `decide +kernel`.
Python with exact integers: worst case `p = 3`, margin 1.0031 at 1024, 0.9926 at 64, so the
coarser table of DDCase4 would fail here; true margin 1.0045.

CONDITIONAL ON `RSHyp` only: `case2`, `Case2Script N` for every `N`. PROVED, no input: `fin_bound`, `head_bound`.
CONDITIONAL ON `RSHyp` only: `lemma2_1_of_RS`, Lemma 2.1 with `K = 3` for integer `w ≥ 2`.
Goldbach is open.
-/
import Mathlib
import LeanLab.AlmostPrimes.DDCase4

open Real Finset LeanLab.AlmostPrimes.DDLemma21 LeanLab.AlmostPrimes.DDLemma21All
  LeanLab.AlmostPrimes.DDCase4

namespace LeanLab.AlmostPrimes.DDCase2

/-- The common denominator of the finer log table. -/
def E : ℕ := 1024

/-- `(p, u)` for the 60 odd primes `p < 286`, with `p^1024 ≤ 2^u`. -/
def T2 : List (ℕ × ℕ) :=
  [(3, 1624),
  (5, 2378),
  (7, 2875),
  (11, 3543),
  (13, 3790),
  (17, 4186),
  (19, 4350),
  (23, 4633),
  (29, 4975),
  (31, 5074),
  (37, 5335),
  (41, 5487),
  (43, 5557),
  (47, 5688),
  (53, 5866),
  (59, 6024),
  (61, 6074),
  (67, 6212),
  (71, 6298),
  (73, 6339),
  (79, 6456),
  (83, 6529),
  (89, 6632),
  (97, 6759),
  (101, 6819),
  (103, 6847),
  (107, 6904),
  (109, 6931),
  (113, 6984),
  (127, 7157),
  (131, 7203),
  (137, 7269),
  (139, 7290),
  (149, 7393),
  (151, 7413),
  (157, 7470),
  (163, 7526),
  (167, 7561),
  (173, 7614),
  (179, 7664),
  (181, 7680),
  (191, 7760),
  (193, 7775),
  (197, 7805),
  (199, 7820),
  (211, 7907),
  (223, 7989),
  (227, 8015),
  (229, 8028),
  (233, 8053),
  (239, 8091),
  (241, 8103),
  (251, 8163),
  (257, 8198),
  (263, 8232),
  (269, 8266),
  (271, 8277),
  (277, 8309),
  (281, 8330),
  (283, 8341)]

/-- `2^L286 ≤ 286^1024`. -/
def L286 : ℕ := 8355

def tabCheck : Bool := 2 ^ L286 ≤ 286 ^ E && T2.all fun e => e.1 ^ E ≤ 2 ^ e.2

def finCheck : Bool := T2.all fun e =>
  124 * num e.1 283 * e.2 ^ 2 ≤ 186 * L286 ^ 2 * den e.1 283

theorem tabCheck_ok : tabCheck = true := by decide +kernel

theorem finCheck_ok : finCheck = true := by decide +kernel

theorem T2_keys : PL.filter (fun r => 3 ≤ r) = T2.map Prod.fst := by decide +kernel

theorem PL_le : ∀ n ∈ PL, n ≤ 283 := by decide +kernel

lemma mem_primesIn {a b : ℝ} (r : ℕ) : r ∈ primesIn a b ↔ r.Prime ∧ a ≤ r ∧ (r : ℝ) < b := by
  simp only [primesIn, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, h⟩; exact h
  · rintro h; exact ⟨Nat.lt_ceil.mpr h.2.2, h⟩

lemma primesIn_split {w z : ℝ} (hw : w ≤ 286) (hz : 286 ≤ z) :
    primesIn w z = primesIn w 286 ∪ primesIn 286 z := by
  ext r
  simp only [Finset.mem_union, mem_primesIn]
  constructor
  · rintro ⟨hp, h1, h2⟩
    by_cases h : (r : ℝ) < 286
    · exact Or.inl ⟨hp, h1, h⟩
    · push Not at h; exact Or.inr ⟨hp, h, h2⟩
  · rintro (⟨hp, h1, h2⟩ | ⟨hp, h1, h2⟩)
    · exact ⟨hp, h1, by linarith⟩
    · exact ⟨hp, by linarith, h2⟩

lemma primesIn_disj (w z : ℝ) : Disjoint (primesIn w 286) (primesIn 286 z) := by
  rw [Finset.disjoint_left]
  intro r h1 h2
  rw [mem_primesIn] at h1 h2
  linarith [h1.2.2, h2.2.1]

lemma prod_nonneg' (N : ℕ) (a b : ℝ) : 0 ≤ ∏ r ∈ primesIn a b, (1 - g N r)⁻¹ :=
  Finset.prod_nonneg fun r hr => factor_nonneg N r ((mem_primesIn r).mp hr).1

/-- The tail `[286, z)`, from Case 1, CONDITIONAL ON `RSHyp`. -/
lemma tail_bound (N : ℕ) (hRS : RSHyp) {z : ℝ} (hz : 286 ≤ z) :
    ∏ r ∈ primesIn 286 z, (1 - g N r)⁻¹ ≤ 1.24 * (log z / log 286) ^ 2 := by
  rcases hz.lt_or_eq with hz' | rfl
  · exact lemma2_1_case1 N 286 z (le_refl _) hz' (hRS 286 z (le_refl _) hz')
  · have he : primesIn 286 286 = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro r hr; rw [mem_primesIn] at hr; linarith [hr.2.1, hr.2.2]
    have hl : (0 : ℝ) < log 286 := log_pos (by norm_num)
    rw [he, Finset.prod_empty, div_self hl.ne']; norm_num

lemma log_hi2 {n u : ℕ} (hn : 1 ≤ n) (h : n ^ E ≤ 2 ^ u) :
    log (n : ℝ) ≤ (u : ℝ) * log 2 / 1024 := by
  have h' : (n : ℝ) ^ E ≤ ((2 : ℕ) : ℝ) ^ u := by exact_mod_cast h
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have := Real.log_le_log (by positivity) h'
  rw [Real.log_pow, Real.log_pow] at this
  push_cast at this
  simp only [E] at this
  push_cast at this
  rw [le_div_iff₀ (by norm_num)]; linarith

lemma log286_lo : (L286 : ℝ) * log 2 / 1024 ≤ log 286 := by
  have hc := tabCheck_ok
  simp only [tabCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  have h' : ((2 : ℕ) : ℝ) ^ L286 ≤ ((286 : ℕ) : ℝ) ^ E := by exact_mod_cast hc.1
  have := Real.log_le_log (by positivity) h'
  rw [Real.log_pow, Real.log_pow] at this
  simp only [E] at this
  push_cast at this
  rw [div_le_iff₀ (by norm_num)]; linarith

/-- The finite part: for an odd prime `p < 286` and `0 < w ≤ p`,
`1.24 · H(p) · log² w ≤ 1.86 · log² 286`. -/
lemma fin_bound {p : ℕ} (hp : p ∈ PL) (hp3 : 3 ≤ p) {w : ℝ} (hw : 1 ≤ w) (hwp : w ≤ p) :
    (num p 283 : ℝ) / (den p 283 : ℝ) * 1.24 * (log w) ^ 2 ≤ 1.86 * (log 286) ^ 2 := by
  have hkey : p ∈ T2.map Prod.fst := by
    rw [← T2_keys]; exact List.mem_filter.mpr ⟨hp, by simpa using hp3⟩
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hkey
  have hc := tabCheck_ok
  simp only [tabCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  have hf := finCheck_ok
  simp only [finCheck, List.all_eq_true, decide_eq_true_eq] at hf
  have hfe := hf e he
  have hu := log_hi2 (by omega) (hc.2 e he)
  have hL := log286_lo
  clear hc hf
  have hden : 0 < den e.1 283 := by
    unfold den
    apply List.prod_pos
    intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    have := PL_two_le r (List.mem_of_mem_filter hr)
    unfold hd; split_ifs <;> omega
  have hden' : (0 : ℝ) < den e.1 283 := by exact_mod_cast hden
  have hfe' : (124 : ℝ) * num e.1 283 * (e.2 : ℝ) ^ 2 ≤ 186 * (L286 : ℝ) ^ 2 * den e.1 283 := by
    exact_mod_cast hfe
  set H := (num e.1 283 : ℝ) / (den e.1 283 : ℝ) with hH
  have hH0 : 0 ≤ H := div_nonneg (Nat.cast_nonneg _) hden'.le
  have hHu : H * 1.24 * (e.2 : ℝ) ^ 2 ≤ 1.86 * (L286 : ℝ) ^ 2 := by
    have : (num e.1 283 : ℝ) = H * den e.1 283 := by rw [hH]; field_simp
    rw [this] at hfe'
    have h2 : (H * 1.24 * (e.2 : ℝ) ^ 2 - 1.86 * (L286 : ℝ) ^ 2) * (den e.1 283 : ℝ) ≤ 0 := by
      have e0 : (H * 1.24 * (e.2 : ℝ) ^ 2 - 1.86 * (L286 : ℝ) ^ 2) * (den e.1 283 : ℝ) =
          ((124 : ℝ) * (H * den e.1 283) * (e.2 : ℝ) ^ 2 - 186 * (L286 : ℝ) ^ 2 * den e.1 283) / 100 := by
        ring
      rw [e0]
      have : (124 : ℝ) * (H * den e.1 283) * (e.2 : ℝ) ^ 2 - 186 * (L286 : ℝ) ^ 2 * den e.1 283 ≤ 0 := by
        linarith
      linarith
    have := (mul_nonpos_iff.mp h2)
    rcases this with ⟨_, h⟩ | ⟨h, _⟩
    · linarith
    · linarith
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hlw0 : 0 ≤ log w := log_nonneg hw
  have hlwp : log w ≤ log (e.1 : ℝ) := log_le_log (by linarith) hwp
  have hsq1 : (log w) ^ 2 ≤ ((e.2 : ℝ) * log 2 / 1024) ^ 2 :=
    pow_le_pow_left₀ hlw0 (hlwp.trans hu) 2
  have hsq2 : ((L286 : ℝ) * log 2 / 1024) ^ 2 ≤ (log 286) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hL 2
  set c := (log 2 / 1024) ^ 2 with hc'
  have hc0 : 0 ≤ c := sq_nonneg _
  have e1 : ((e.2 : ℝ) * log 2 / 1024) ^ 2 = (e.2 : ℝ) ^ 2 * c := by rw [hc']; ring
  have e2 : ((L286 : ℝ) * log 2 / 1024) ^ 2 = (L286 : ℝ) ^ 2 * c := by rw [hc']; ring
  rw [e1] at hsq1; rw [e2] at hsq2
  calc H * 1.24 * (log w) ^ 2 ≤ H * 1.24 * ((e.2 : ℝ) ^ 2 * c) :=
        mul_le_mul_of_nonneg_left hsq1 (by positivity)
    _ = (H * 1.24 * (e.2 : ℝ) ^ 2) * c := by ring
    _ ≤ (1.86 * (L286 : ℝ) ^ 2) * c := mul_le_mul_of_nonneg_right hHu hc0
    _ = 1.86 * ((L286 : ℝ) ^ 2 * c) := by ring
    _ ≤ 1.86 * (log 286) ^ 2 := by linarith

/-- The finite product `A = ∏_{w ≤ p < 286}` satisfies `1.24 · A · log² w ≤ 1.86 · log² 286`. -/
lemma head_bound (N w : ℕ) (hw : 3 ≤ w) (hw' : w ≤ 285) :
    (∏ r ∈ primesIn w 286, (1 - g N r)⁻¹) * 1.24 * (log (w : ℝ)) ^ 2 ≤ 1.86 * (log 286) ^ 2 := by
  have hw3 : (3 : ℝ) ≤ w := by exact_mod_cast hw
  have hlw0 : 0 ≤ log (w : ℝ) := log_nonneg (by linarith)
  set S := primesIn (w : ℝ) 286 with hS
  rcases S.eq_empty_or_nonempty with he | hne
  · rw [he, Finset.prod_empty]
    have : log (w : ℝ) ≤ log 286 := log_le_log (by linarith) (by exact_mod_cast (by omega : w ≤ 286))
    have : (log (w : ℝ)) ^ 2 ≤ (log 286) ^ 2 := pow_le_pow_left₀ hlw0 this 2
    nlinarith
  set p := S.min' hne
  have hpS := (mem_primesIn p).mp (S.min'_mem hne)
  have hlt : ∀ r ∈ S, r < 286 := by
    intro r hr
    have : (r : ℝ) < 286 := ((mem_primesIn r).mp hr).2.2
    exact_mod_cast this
  have hpPL : p ∈ PL := (prime_iff_mem p (hlt p (S.min'_mem hne))).mp hpS.1
  have hp3 : 3 ≤ p := by
    have : (3 : ℝ) ≤ p := le_trans hw3 hpS.2.1
    exact_mod_cast this
  have hseg : S = (seg p 283).toFinset := by
    ext r
    simp only [List.mem_toFinset, seg, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · intro hr
      have hrPL := (prime_iff_mem r (hlt r hr)).mp ((mem_primesIn r).mp hr).1
      exact ⟨hrPL, S.min'_le r hr, PL_le r hrPL⟩
    · rintro ⟨hrPL, hpr, _⟩
      rw [hS, mem_primesIn]
      refine ⟨(prime_iff_mem r (PL_lt r hrPL)).mpr hrPL, ?_, ?_⟩
      · have : (p : ℝ) ≤ r := by exact_mod_cast hpr
        linarith [hpS.2.1]
      · have := PL_lt r hrPL
        exact_mod_cast this
  have hnd : (seg p 283).Nodup := PL_nodup.filter _
  have hprod : ∏ r ∈ S, (1 - g N r)⁻¹ ≤ (num p 283 : ℝ) / (den p 283 : ℝ) := by
    calc ∏ r ∈ S, (1 - g N r)⁻¹ ≤ ∏ r ∈ S, ((hn r : ℝ) / (hd r : ℝ)) := by
          apply Finset.prod_le_prod₀
          · intro r hr; exact factor_nonneg N r ((mem_primesIn r).mp hr).1
          · intro r hr; exact factor_le N r ((mem_primesIn r).mp hr).1
      _ = (∏ r ∈ S, (hn r : ℝ)) / (∏ r ∈ S, (hd r : ℝ)) := Finset.prod_div_distrib _ _
      _ = (num p 283 : ℝ) / (den p 283 : ℝ) := by
          rw [← Nat.cast_prod, ← Nat.cast_prod, hseg, List.prod_toFinset _ hnd,
            List.prod_toFinset _ hnd]
          rfl
  have hfb := fin_bound hpPL hp3 (w := (w : ℝ)) (by linarith) hpS.2.1
  have hsq0 : 0 ≤ (log (w : ℝ)) ^ 2 := sq_nonneg _
  have := mul_le_mul_of_nonneg_right hprod (by positivity : (0 : ℝ) ≤ 1.24 * (log (w : ℝ)) ^ 2)
  calc (∏ r ∈ S, (1 - g N r)⁻¹) * 1.24 * (log (w : ℝ)) ^ 2
      = (∏ r ∈ S, (1 - g N r)⁻¹) * (1.24 * (log (w : ℝ)) ^ 2) := by ring
    _ ≤ (num p 283 : ℝ) / (den p 283 : ℝ) * (1.24 * (log (w : ℝ)) ^ 2) := this
    _ = (num p 283 : ℝ) / (den p 283 : ℝ) * 1.24 * (log (w : ℝ)) ^ 2 := by ring
    _ ≤ 1.86 * (log 286) ^ 2 := hfb

/-- **Dudek-Dunn Lemma 2.1, Case 2**, `K ≤ 1.86` for `3 ≤ w ≤ 285`, `z ≥ 286`.
CONDITIONAL ON `RSHyp` only, as in the paper, whose Case 2 bounds its tail by Case 1. -/
theorem case2 (N : ℕ) (hRS : RSHyp) : Case2Script N := by
  intro w hw hw' z hz
  have hw3 : (3 : ℝ) ≤ w := by exact_mod_cast hw
  have hw286 : (w : ℝ) ≤ 286 := by exact_mod_cast (by omega : w ≤ 286)
  rw [primesIn_split hw286 hz, Finset.prod_union (primesIn_disj _ _)]
  set A := ∏ r ∈ primesIn (w : ℝ) 286, (1 - g N r)⁻¹
  set B := ∏ r ∈ primesIn 286 z, (1 - g N r)⁻¹
  have hA0 : 0 ≤ A := prod_nonneg' N _ _
  have hB := tail_bound N hRS hz
  have hhead := head_bound N w hw hw'
  have hlw : 0 < log (w : ℝ) := log_pos (by linarith)
  have hl286 : 0 < log (286 : ℝ) := log_pos (by norm_num)
  set a := log (w : ℝ)
  set c := log (286 : ℝ)
  set x := log z
  have hAB : A * B ≤ A * (1.24 * (x / c) ^ 2) := mul_le_mul_of_nonneg_left hB hA0
  have hfin : A * (1.24 * (x / c) ^ 2) ≤ 1.86 * (x / a) ^ 2 := by
    rw [div_pow, div_pow]
    have hx2 : 0 ≤ x ^ 2 := sq_nonneg _
    have ha2 : 0 < a ^ 2 := by positivity
    have hc2 : 0 < c ^ 2 := by positivity
    rw [show A * (1.24 * (x ^ 2 / c ^ 2)) = (A * 1.24 * a ^ 2) * x ^ 2 / (a ^ 2 * c ^ 2) by
          field_simp,
        show 1.86 * (x ^ 2 / a ^ 2) = (1.86 * c ^ 2) * x ^ 2 / (a ^ 2 * c ^ 2) by field_simp]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right hhead hx2
  linarith

/-- **Dudek-Dunn Lemma 2.1**, `K = 3`, for integer `w ≥ 2` and real `z > w`.
CONDITIONAL ON `RSHyp`, Rosser-Schoenfeld Theorem 5 in the form of Case 1, only. -/
theorem lemma2_1_of_RS (N : ℕ) (hRS : RSHyp) (w : ℕ) (hw : 2 ≤ w) (z : ℝ) (hwz : (w : ℝ) < z) :
    ∏ p ∈ primesIn w z, (1 - g N p)⁻¹ ≤ 3 * (log z / log w) ^ 2 :=
  lemma2_1_of_case2 N hRS (case2 N hRS) w hw z hwz

#print axioms tabCheck_ok
#print axioms finCheck_ok
#print axioms fin_bound
#print axioms head_bound
#print axioms case2
#print axioms lemma2_1_of_RS

end LeanLab.AlmostPrimes.DDCase2
