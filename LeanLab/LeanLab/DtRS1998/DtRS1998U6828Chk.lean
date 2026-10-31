/-
P0037 Deshouillers, te Riele, Saouter 1998, Table 1, unit U-6828, run 20261021T0316Z-cloud57.
Checkers for the "worst case" columns of Table 1: for an even W and a range of candidates q,
every odd q in the range gets an entry that rules it out: a proper divisor of q, so q is not
prime; a proper divisor of W - q, so W - q is not prime; or a Fermat witness a with
a^(q-1) ≠ 1 mod q, so q is not prime. A second checker, with no W, shows that a range holds no
prime at all. Soundness proved once here; the tables are checked by `decide +kernel`.
AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import LeanLab.DtRS1998.Pock

namespace LeanLab.DtRS1998.U6828

open LeanLab.Verifications.Pratt

/-- Fermat witness: `0 < a < x` and `a ^ (x - 1) ≠ 1 mod x`. -/
def fermatB (x a : ℕ) : Bool :=
  decide (0 < a) && decide (a < x) && (pm (x.log2 + 1) a (x - 1) x % x != 1 % x)

theorem not_prime_of_fermat {x a : ℕ} (h : fermatB x a = true) : ¬ x.Prime := by
  intro hx
  simp only [fermatB, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨ha0, hax⟩, hne⟩ := h
  haveI := Fact.mk hx
  have hc := pm_cast (x.log2 + 1) a (x - 1) x
    (lt_of_le_of_lt (Nat.sub_le _ _) Nat.lt_log2_self)
  have ha : (a : ZMod x) ≠ 0 := by
    intro h0
    rw [ZMod.natCast_eq_zero_iff] at h0
    have := Nat.le_of_dvd ha0 h0
    omega
  have h1 := ZMod.pow_card_sub_one_eq_one ha
  rw [← hc] at h1
  apply hne
  have := (ZMod.natCast_eq_natCast_iff' _ 1 x).mp (by rw [h1]; simp)
  simpa using this

lemma not_prime_of {t d : ℕ} (h1 : 1 < d) (h2 : d < t) (h3 : t % d = 0) : ¬ t.Prime := by
  intro hp
  have := (Nat.prime_def.mp hp).2 d (Nat.dvd_of_mod_eq_zero h3)
  omega

/-- One entry for the odd number `x`: `(0, d)` a proper divisor of `x`, `(1, d)` a proper
divisor of `e - x`, `(2, a)` a Fermat witness for `x`. -/
def ent (e x : ℕ) : ℕ × ℕ → Bool
  | (w, d) =>
    if w = 0 then 1 < d && d < x && x % d == 0
    else if w = 1 then 1 < d && d < e - x && (e - x) % d == 0
    else fermatB x d

theorem ent_sound {e x : ℕ} {c : ℕ × ℕ} (h : ent e x c = true) (hx : x.Prime) :
    ¬ (e - x).Prime := by
  obtain ⟨w, d⟩ := c
  simp only [ent] at h
  by_cases h0 : w = 0
  · rw [if_pos h0] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact absurd hx (not_prime_of h.1.1 h.1.2 h.2)
  · rw [if_neg h0] at h
    by_cases h1 : w = 1
    · rw [if_pos h1] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
      exact not_prime_of h.1.1 h.1.2 h.2
    · rw [if_neg h1] at h
      exact absurd hx (not_prime_of_fermat h)

/-- Walk `k` numbers from `m`; each odd one consumes the head of `L`. -/
def chkW (e : ℕ) : ℕ → ℕ → List (ℕ × ℕ) → Bool
  | _, 0, _ => true
  | m, k + 1, L =>
    if m % 2 = 0 then chkW e (m + 1) k L else
    match L with
    | [] => false
    | c :: t => ent e m c && chkW e (m + 1) k t

theorem chkW_sound (e : ℕ) : ∀ k m L, 3 ≤ m → chkW e m k L = true →
    ∀ x, m ≤ x → x < m + k → x.Prime → ¬ (e - x).Prime := by
  intro k
  induction k with
  | zero => intro m L _ _ x h1 h2; omega
  | succ k ih =>
    intro m L hm h x h1 h2 hx
    unfold chkW at h
    by_cases hev : m % 2 = 0
    · rw [if_pos hev] at h
      by_cases hxm : x = m
      · subst hxm
        exfalso
        have := hx.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero hev); omega
      · exact ih (m + 1) L (by omega) h x (by omega) (by omega) hx
    · rw [if_neg hev] at h
      match L, h with
      | c :: t, h =>
        simp only [Bool.and_eq_true] at h
        by_cases hxm : x = m
        · subst hxm
          exact ent_sound h.1 hx
        · exact ih (m + 1) t (by omega) h.2 x (by omega) (by omega) hx

/-- One entry ruling out `x` itself: `(0, d)` a proper divisor, `(2, a)` a Fermat witness. -/
def entN (x : ℕ) : ℕ × ℕ → Bool
  | (w, d) => if w = 0 then 1 < d && d < x && x % d == 0 else fermatB x d

theorem entN_sound {x : ℕ} {c : ℕ × ℕ} (h : entN x c = true) : ¬ x.Prime := by
  obtain ⟨w, d⟩ := c
  simp only [entN] at h
  by_cases h0 : w = 0
  · rw [if_pos h0] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact not_prime_of h.1.1 h.1.2 h.2
  · rw [if_neg h0] at h
    exact not_prime_of_fermat h

/-- Walk `k` numbers from `m`; no prime among them. -/
def chkN : ℕ → ℕ → List (ℕ × ℕ) → Bool
  | _, 0, _ => true
  | m, k + 1, L =>
    if m % 2 = 0 then chkN (m + 1) k L else
    match L with
    | [] => false
    | c :: t => entN m c && chkN (m + 1) k t

theorem chkN_sound : ∀ k m L, 3 ≤ m → chkN m k L = true →
    ∀ x, m ≤ x → x < m + k → ¬ x.Prime := by
  intro k
  induction k with
  | zero => intro m L _ _ x h1 h2; omega
  | succ k ih =>
    intro m L hm h x h1 h2 hx
    unfold chkN at h
    by_cases hev : m % 2 = 0
    · rw [if_pos hev] at h
      by_cases hxm : x = m
      · subst hxm
        have := hx.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero hev); omega
      · exact ih (m + 1) L (by omega) h x (by omega) (by omega) hx
    · rw [if_neg hev] at h
      match L, h with
      | c :: t, h =>
        simp only [Bool.and_eq_true] at h
        by_cases hxm : x = m
        · subst hxm
          exact entN_sound h.1 hx
        · exact ih (m + 1) t (by omega) h.2 x (by omega) (by omega) hx

/-- Join two ranges. -/
theorem join {P : ℕ → Prop} {a b c : ℕ} (h1 : ∀ x, a ≤ x → x < b → P x)
    (h2 : ∀ x, b ≤ x → x < c → P x) : ∀ x, a ≤ x → x < c → P x := by
  intro x hx1 hx2
  by_cases hb : x < b
  · exact h1 x hx1 hb
  · exact h2 x (by omega) hx2

/-- A prime from a one-entry Pocklington chain check. -/
theorem prime_of_chain {S : List Big.Cert} (hS : Big.chainP [] S = true) {p : ℕ}
    (hp : p ∈ S.map Prod.fst) : p.Prime := by
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
  exact Big.chainP_sound S [] (by simp) hS c hc

/-- Sanity: 341 = 11 · 31 is a base 3 Fermat composite. -/
example : ¬ (341 : ℕ).Prime := not_prime_of_fermat (a := 3) (by decide +kernel)

end LeanLab.DtRS1998.U6828
