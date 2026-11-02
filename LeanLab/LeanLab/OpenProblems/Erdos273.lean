import Mathlib

/-!
# Erdős Problem 273, OPEN, sealed statement and closable sub-claims

Unit U-1603, 2026-11-02. AI wrote the Lean code. An OPEN problem, a target for the network, no
claim of progress on it.

Plain math: is there a covering system of the integers with distinct moduli, all of the form
`p - 1` for primes `p ≥ 5`? Selfridge found one using divisors of 360 if `p = 3` is allowed.

Source: T. F. Bloom, Erdős Problem #273, https://www.erdosproblems.com/273. The page itself was
refused by robots rules on 2026-11-02 and that was not worked around. Read instead, both fetched
2026-11-02: the site's https://www.erdosproblems.com/history/273, which shows one revision dated
2025-10-20 with this statement and the Selfridge remark but no explicit status, and
google-deepmind/formal-conjectures `FormalConjectures/ErdosProblems/273.lean`, where `erdos_273` is
tagged `research open` and `erdos_273.variants.three` is tagged `research solved` and left as sorry
with a TODO asking for a reference. So OPEN rests on FC and on the history page, not on a status
line of the problem page. Recheck the page before any claim.

Definition reused in substance from formal-conjectures, Copyright 2025 The Formal Conjectures
Authors, Apache-2.0: FC writes `StrictCoveringSystem ℤ` with moduli `Ideal.span {↑(p - 1)}`, a
finite family of cosets of proper nonzero ideals with injective moduli. `CoverBy` below says the
same with a `Finset` of pairs, using Mathlib only, since FC's structure is in its own library. The
two are not proved equivalent here. Note FC states the variant over `ℕ` and the main one over `ℤ`.

Why it is here: a single explicit covering settles the question, and the Lean kernel can check
one. That is the proof by computation plus Lean that the screen asks for. The lab already uses
covering systems in `Romanov/Erdos.lean`. Lab numerics, greedy search only: with moduli dividing
43243200 the reciprocal sum is 1.187 and 8 percent stays uncovered, so no covering has been found.

Status of the sub-claims: KNOWN, none ORIGINAL. `cover_three` is Selfridge's remark, proved with
an explicit system; no such Lean proof is in FC, which is a formal gap, not new mathematics.
`exists_modulus_ge_70` is the standard density bound with an explicit constant.
-/

namespace LeanLab.OpenProblems.Erdos273

/-- `S` is a finite list of pairs modulus, residue; every integer lies in one class. -/
def Covers (S : Finset (ℕ × ℤ)) : Prop := ∀ x : ℤ, ∃ s ∈ S, (s.1 : ℤ) ∣ x - s.2

/-- A covering system with distinct moduli, each `p - 1` for a prime `p ≥ lo`. -/
def CoverBy (lo : ℕ) : Prop :=
  ∃ S : Finset (ℕ × ℤ), Covers S ∧ Set.InjOn Prod.fst (S : Set (ℕ × ℤ)) ∧
    ∀ s ∈ S, ∃ p : ℕ, p.Prime ∧ lo ≤ p ∧ s.1 = p - 1

/-- **Erdős 273, OPEN, sealed.** An explicit covering proves it, and a proof of the negation is
also new knowledge. -/
def Erdos273Statement : Prop := CoverBy 5

/-! ### Vacuity -/

/-- The empty family covers nothing. -/
theorem not_covers_empty : ¬ Covers ∅ := fun h => by simpa using h 0

/-- With `p = 2` allowed the question is trivial, modulus 1, which FC's `ne_top` excludes, so the
bound on `p` carries weight. -/
theorem coverBy_two : CoverBy 2 := by
  refine ⟨{(1, 0)}, fun x => ⟨(1, 0), by simp, by simp⟩, by simp, ?_⟩
  intro s hs
  obtain rfl : s = (1, 0) := by simpa using hs
  exact ⟨2, Nat.prime_two, le_rfl, rfl⟩

theorem coverBy_mono {a b : ℕ} (h : a ≤ b) : CoverBy b → CoverBy a := by
  rintro ⟨S, hc, hi, hp⟩
  refine ⟨S, hc, hi, fun s hs => ?_⟩
  obtain ⟨p, hpp, hb, hs⟩ := hp s hs
  exact ⟨p, hpp, h.trans hb, hs⟩

/-! ### Selfridge's variant, `p = 3` allowed -/

/-- An explicit system with divisors of 360, found by exhaustive search. Pairs modulus, residue. -/
def selfridge : Finset (ℕ × ℤ) :=
  {(2, 0), (4, 1), (6, 3), (10, 7), (12, 11), (18, 1), (30, 1), (36, 7), (40, 23), (60, 19),
    (72, 67), (180, 175)}

theorem selfridge_mod : ∀ r : Fin 360, ∃ s ∈ selfridge, (r.val : ℤ) % (s.1 : ℤ) = s.2 % (s.1 : ℤ) := by
  decide +kernel

theorem selfridge_dvd : ∀ s ∈ selfridge, (s.1 : ℤ) ∣ 360 := by decide +kernel

theorem covers_selfridge : Covers selfridge := by
  intro x
  have hr0 : 0 ≤ x % 360 := Int.emod_nonneg _ (by norm_num)
  have hr1 : x % 360 < 360 := Int.emod_lt_of_pos _ (by norm_num)
  obtain ⟨s, hs, h⟩ := selfridge_mod ⟨(x % 360).toNat, by omega⟩
  refine ⟨s, hs, ?_⟩
  simp only at h
  rw [Int.toNat_of_nonneg hr0] at h
  have h1 : (s.1 : ℤ) ∣ x - x % 360 := by
    refine (selfridge_dvd s hs).trans ?_
    exact ⟨x / 360, by have := Int.emod_add_mul_ediv x 360; omega⟩
  have h2 : (s.1 : ℤ) ∣ x % 360 - s.2 := Int.ModEq.dvd (Int.ModEq.symm h)
  have := dvd_add h1 h2
  simpa using this

/-- **Closable sub-claim, PROVED, KNOWN.** Selfridge's example: a covering system with distinct
moduli of the form `p - 1`, `p ≥ 3`, all divisors of 360. -/
theorem cover_three : CoverBy 3 := by
  refine ⟨selfridge, covers_selfridge, ?_, ?_⟩
  · intro a ha b hb hab
    have ha' : a ∈ selfridge := ha
    have hb' : b ∈ selfridge := hb
    revert hab
    revert a b
    decide +kernel
  · intro s hs
    simp only [selfridge, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨3, by norm_num, by norm_num, rfl⟩
    · exact ⟨5, by norm_num, by norm_num, rfl⟩
    · exact ⟨7, by norm_num, by norm_num, rfl⟩
    · exact ⟨11, by norm_num, by norm_num, rfl⟩
    · exact ⟨13, by norm_num, by norm_num, rfl⟩
    · exact ⟨19, by norm_num, by norm_num, rfl⟩
    · exact ⟨31, by norm_num, by norm_num, rfl⟩
    · exact ⟨37, by norm_num, by norm_num, rfl⟩
    · exact ⟨41, by norm_num, by norm_num, rfl⟩
    · exact ⟨61, by norm_num, by norm_num, rfl⟩
    · exact ⟨73, by norm_num, by norm_num, rfl⟩
    · exact ⟨181, by norm_num, by norm_num, rfl⟩

/-! ### The certificate shape for a search winner -/

/-- Every residue in `[0, M)` lies in a class of `L`. Pairs modulus, residue. -/
def checkCover (M : ℕ) (L : List (ℕ × ℤ)) : Bool :=
  (List.range M).all fun r => L.any fun s => decide (((r : ℤ) - s.2) % (s.1 : ℤ) = 0)

/-- **PROVED.** A finite check over one common multiple `M` of the moduli gives a covering. -/
theorem covers_of_check {M : ℕ} {L : List (ℕ × ℤ)} (hM : 0 < M)
    (hdvd : ∀ s ∈ L, (s.1 : ℤ) ∣ (M : ℤ)) (h : checkCover M L = true) : Covers L.toFinset := by
  intro x
  have hM' : (0 : ℤ) < M := by exact_mod_cast hM
  have hr0 : 0 ≤ x % (M : ℤ) := Int.emod_nonneg _ hM'.ne'
  have hr1 : x % (M : ℤ) < M := Int.emod_lt_of_pos _ hM'
  simp only [checkCover, List.all_eq_true, List.mem_range, List.any_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨s, hs, hmod⟩ := h (x % (M : ℤ)).toNat (by omega)
  refine ⟨s, List.mem_toFinset.mpr hs, ?_⟩
  rw [Int.toNat_of_nonneg hr0] at hmod
  have h1 : (s.1 : ℤ) ∣ x - x % (M : ℤ) := by
    refine (hdvd s hs).trans ?_
    exact ⟨x / M, by have := Int.emod_add_mul_ediv x M; omega⟩
  have h2 : (s.1 : ℤ) ∣ x % (M : ℤ) - s.2 := Int.dvd_of_emod_eq_zero hmod
  have := dvd_add h1 h2
  simpa using this

/-- **PROVED.** How a search winner closes the sealed Prop: a list with distinct moduli, each
`p - 1` for a prime `p ≥ 5`, passing `checkCover`, proves `Erdos273Statement`. No list is known;
this is the target shape, not progress. -/
theorem statement_of_check {M : ℕ} {L : List (ℕ × ℤ)} (hM : 0 < M)
    (hdvd : ∀ s ∈ L, (s.1 : ℤ) ∣ (M : ℤ)) (hinj : (L.map Prod.fst).Nodup)
    (hp : ∀ s ∈ L, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ s.1 = p - 1) (h : checkCover M L = true) :
    Erdos273Statement := by
  refine ⟨L.toFinset, covers_of_check hM hdvd h, ?_, ?_⟩
  · intro a ha b hb hab
    exact List.inj_on_of_nodup_map hinj (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
  · exact fun s hs => hp s (List.mem_toFinset.mp hs)

/-- The check accepts Selfridge's system, so `checkCover` is not vacuous. -/
theorem check_selfridge :
    checkCover 360 [(2, 0), (4, 1), (6, 3), (10, 7), (12, 11), (18, 1), (30, 1), (36, 7), (40, 23),
      (60, 19), (72, 67), (180, 175)] = true := by decide +kernel

/-! ### The density bound -/

/-- At most `M / d` integers in `[0, M)` lie in one class mod `d`, when `d ∣ M`. -/
theorem card_class_le {M d : ℕ} (hd : 0 < d) (hdM : d ∣ M) (a : ℤ) :
    ((Finset.range M).filter fun x : ℕ => (d : ℤ) ∣ (x : ℤ) - a).card ≤ M / d := by
  rw [← Finset.card_range (M / d)]
  refine Finset.card_le_card_of_injOn (fun x => x / d) ?_ ?_
  · intro x hx
    have hx' : x < M := by simpa using (Finset.mem_filter.mp hx).1
    simp only [Finset.coe_range, Set.mem_Iio]
    obtain ⟨c, rfl⟩ := hdM
    rw [Nat.mul_div_cancel_left _ hd]
    exact Nat.div_lt_of_lt_mul hx'
  · intro x hx y hy hxy
    have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
    have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2
    have hdvd : (d : ℤ) ∣ (x : ℤ) - y := by
      have := dvd_sub h1 h2
      simpa using this
    simp only at hxy
    have hxe := Nat.div_add_mod x d
    have hye := Nat.div_add_mod y d
    rw [hxy] at hxe
    have hmod : (d : ℤ) ∣ ((x % d : ℕ) : ℤ) - ((y % d : ℕ) : ℤ) := by
      have : ((x : ℤ) - y) = ((x % d : ℕ) : ℤ) - ((y % d : ℕ) : ℤ) := by
        have h3 : (x : ℤ) = (d * (y / d) : ℕ) + ((x % d : ℕ) : ℤ) := by exact_mod_cast hxe.symm
        have h4 : (y : ℤ) = (d * (y / d) : ℕ) + ((y % d : ℕ) : ℤ) := by exact_mod_cast hye.symm
        omega
      rwa [← this]
    have hlx := Nat.mod_lt x hd
    have hly := Nat.mod_lt y hd
    have : ((x % d : ℕ) : ℤ) - ((y % d : ℕ) : ℤ) = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd hmod
      rw [abs_lt]
      constructor <;> omega
    omega

/-- **PROVED, KNOWN, standard.** The reciprocals of the moduli of a covering sum to at least 1. -/
theorem one_le_sum_inv {S : Finset (ℕ × ℤ)} (hS : Covers S) (hpos : ∀ s ∈ S, 0 < s.1) :
    (1 : ℚ) ≤ ∑ s ∈ S, (1 : ℚ) / s.1 := by
  set M : ℕ := ∏ s ∈ S, s.1 with hM
  have hMpos : 0 < M := Finset.prod_pos hpos
  have hsub : Finset.range M ⊆ S.biUnion fun s =>
      (Finset.range M).filter fun x : ℕ => (s.1 : ℤ) ∣ (x : ℤ) - s.2 := by
    intro x hx
    obtain ⟨s, hs, h⟩ := hS x
    exact Finset.mem_biUnion.mpr ⟨s, hs, Finset.mem_filter.mpr ⟨hx, h⟩⟩
  have hcard : M ≤ ∑ s ∈ S, M / s.1 := by
    calc M = (Finset.range M).card := (Finset.card_range M).symm
      _ ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_biUnion_le
      _ ≤ _ := Finset.sum_le_sum fun s hs =>
        card_class_le (hpos s hs) (Finset.dvd_prod_of_mem _ hs) s.2
  have hq : (M : ℚ) ≤ ∑ s ∈ S, (M : ℚ) * ((1 : ℚ) / s.1) := by
    calc (M : ℚ) ≤ ((∑ s ∈ S, M / s.1 : ℕ) : ℚ) := by exact_mod_cast hcard
      _ = ∑ s ∈ S, ((M / s.1 : ℕ) : ℚ) := by push_cast; rfl
      _ ≤ _ := by
        refine Finset.sum_le_sum fun s hs => ?_
        rw [mul_one_div]
        exact Nat.cast_div_le
  rw [← Finset.mul_sum] at hq
  have hMq : (0 : ℚ) < M := by exact_mod_cast hMpos
  exact le_of_mul_le_mul_left (by simpa using hq) hMq

/-- The allowed moduli below 70: `p - 1` for primes `5 ≤ p ≤ 67`. -/
def lowModuli : Finset ℕ := {4, 6, 10, 12, 16, 18, 22, 28, 30, 36, 40, 42, 46, 52, 58, 60, 66}

theorem low_sum_lt : ∑ d ∈ lowModuli, (1 : ℚ) / d < 1 := by
  simp only [lowModuli]
  norm_num [Finset.sum_insert, Finset.sum_singleton]

theorem mem_lowModuli {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h : p - 1 < 70) :
    p - 1 ∈ lowModuli := by
  have hp70 : p ≤ 70 := by omega
  interval_cases p <;> first | (exfalso; revert hp; norm_num; done) | decide

/-- **Closable sub-claim, PROVED, KNOWN, standard.** Any covering as in Erdős 273 has a modulus at
least 70, since the seventeen allowed moduli below 70 have reciprocal sum `160107799/160240080`,
below 1. Lower bound only: it says no small system works, nothing about existence. -/
theorem exists_modulus_ge_70 {S : Finset (ℕ × ℤ)} (hS : Covers S)
    (hi : Set.InjOn Prod.fst (S : Set (ℕ × ℤ)))
    (hp : ∀ s ∈ S, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ s.1 = p - 1) : ∃ s ∈ S, 70 ≤ s.1 := by
  by_contra hcon
  push Not at hcon
  have hpos : ∀ s ∈ S, 0 < s.1 := by
    intro s hs
    obtain ⟨p, -, h5, h⟩ := hp s hs
    omega
  have hsub : S.image Prod.fst ⊆ lowModuli := by
    intro d hd
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨p, hpp, h5, h⟩ := hp s hs
    rw [h]
    exact mem_lowModuli hpp h5 (h ▸ hcon s hs)
  have h1 := one_le_sum_inv hS hpos
  have h2 : ∑ s ∈ S, (1 : ℚ) / s.1 = ∑ d ∈ S.image Prod.fst, (1 : ℚ) / d :=
    (Finset.sum_image (f := fun d : ℕ => (1 : ℚ) / d) hi).symm
  have h3 : ∑ d ∈ S.image Prod.fst, (1 : ℚ) / d ≤ ∑ d ∈ lowModuli, (1 : ℚ) / d :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
  have := low_sum_lt
  linarith

end LeanLab.OpenProblems.Erdos273

#print axioms LeanLab.OpenProblems.Erdos273.not_covers_empty
#print axioms LeanLab.OpenProblems.Erdos273.coverBy_two
#print axioms LeanLab.OpenProblems.Erdos273.cover_three
#print axioms LeanLab.OpenProblems.Erdos273.one_le_sum_inv
#print axioms LeanLab.OpenProblems.Erdos273.exists_modulus_ge_70
#print axioms LeanLab.OpenProblems.Erdos273.covers_of_check
#print axioms LeanLab.OpenProblems.Erdos273.statement_of_check
#print axioms LeanLab.OpenProblems.Erdos273.check_selfridge
