/-
P0085 Alsetri 2025, arXiv 2505.09648, Theorem 1.2 in full: for every odd squarefree m with
3 | m, `Alsetri12 m` (the statement of Alsetri2025.lean). Case 5 ∤ m: `alsetri12_of_coprime5`
(AlsetriFinal.lean). Case 5 | m: m = 15 m' with m' squarefree coprime to 30; average f over
the Z_15-fiber, f'(u) = (1/4) Σ_v f(u, v), so Σ f' > φ(m')/2; Alsetri Prop 3.1 mod m'
(`half31_coprime30`) gives a₁, a₂, a₃ with h(f'(aᵢ)) > 0, which is condition (3.1) of
Prop 3.2 for the fibers fᵢ = f(aᵢ, ·); Prop 3.2 (`alsetri_prop32`) finishes, as in the paper.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
-/
import LeanLab.DensityGoldbach.AlsetriFinal
import LeanLab.DensityGoldbach.AlsetriProp32

open Finset

namespace LeanLab.DensityGoldbach

/-- The second CRT coordinate of `z` mod `m' · 15` has the same class mod `3` as `z`. -/
lemma crt15_snd_val3 {m' : ℕ} [NeZero (m' * 15)] (hc : Nat.Coprime m' 15) (z : ZMod (m' * 15)) :
    ((ZMod.chineseRemainder hc z).2).val % 3 = z.val % 3 := by
  have h1 : ZMod.chineseRemainder hc z = ((z.val : ℕ) : ZMod m' × ZMod 15) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val z]
    exact map_natCast (ZMod.chineseRemainder hc) z.val
  rw [h1, Prod.snd_natCast, ZMod.val_natCast, Nat.mod_mod_of_dvd _ (by norm_num : 3 ∣ 15)]

lemma alsetri12_congr {m n : ℕ} (h : m = n) {_ : NeZero m} {_ : NeZero n} (hm : Alsetri12 m) :
    Alsetri12 n := by
  subst h; exact hm

/-- **The step for `5 ∣ m`**: `Half31 m'` and Prop 3.2 give Theorem 1.2 at `m' · 15`. -/
theorem alsetri12_of_half31_15 (m' : ℕ) [NeZero m'] [NeZero (m' * 15)] (hc : Nat.Coprime m' 15)
    (h : Half31 m') : Alsetri12 (m' * 15) := by
  intro f hf hsupp hsum x hx
  set e := ZMod.chineseRemainder hc with he
  set F : ZMod m' → ZMod 15 → ℝ := fun u v => f (e.symm (u, v)) with hF
  have hFs : ∀ u, ∀ v : ZMod 15, v.val % 3 ≠ 1 → F u v = 0 := by
    intro u v hv
    apply hsupp
    rw [← crt15_snd_val3 hc, RingEquiv.apply_symm_apply]
    exact hv
  have hS4 : ∀ u, ∑ v ∈ unitsMod 15, F u v ≤ 4 := by
    intro u
    rw [sum_units15 _ (hFs u)]
    calc ∑ v ∈ U15one, F u v ≤ ∑ v ∈ U15one, (1 : ℝ) := sum_le_sum fun v _ => (hf _).2
      _ = 4 := by rw [sum_const, S15_card]; norm_num
  set f' : ZMod m' → ℝ := fun u => (∑ v ∈ unitsMod 15, F u v) / 4 with hf'
  have hS : ∀ u, ∑ v ∈ unitsMod 15, F u v = 4 * f' u := by intro u; simp only [hf']; ring
  have hf'bd : ∀ u, 0 ≤ f' u ∧ f' u ≤ 1 := by
    intro u
    have h0 : 0 ≤ ∑ v ∈ unitsMod 15, F u v := sum_nonneg fun v _ => (hf _).1
    have := hS4 u
    rw [hS u] at h0 this
    constructor <;> linarith
  have hsum' : 1 / 2 * (m'.totient : ℝ) < ∑ u ∈ unitsMod m', f' u := by
    rw [sum_unitsMod_crt hc, Nat.totient_mul hc, show Nat.totient 15 = 8 by decide] at hsum
    have : ∑ u ∈ unitsMod m', ∑ v ∈ unitsMod 15, F u v = 4 * ∑ u ∈ unitsMod m', f' u := by
      rw [mul_sum]; exact sum_congr rfl fun u _ => hS u
    rw [this] at hsum
    push_cast at hsum
    linarith
  obtain ⟨a₁, ha₁, a₂, ha₂, a₃, ha₃, hx1, hh⟩ := h f' hf'bd hsum' (e x).1
  have hx2 : ((e x).2).val % 3 = 0 := by rw [crt15_snd_val3 hc]; exact hx
  have hT : 2 * ((∑ v ∈ unitsMod 15, F a₁ v) + (∑ v ∈ unitsMod 15, F a₂ v)
      + (∑ v ∈ unitsMod 15, F a₃ v)) <
      (∑ v ∈ unitsMod 15, F a₁ v) * (∑ v ∈ unitsMod 15, F a₂ v)
        + (∑ v ∈ unitsMod 15, F a₂ v) * (∑ v ∈ unitsMod 15, F a₃ v)
        + (∑ v ∈ unitsMod 15, F a₃ v) * (∑ v ∈ unitsMod 15, F a₁ v) := by
    rw [hS a₁, hS a₂, hS a₃]
    unfold hhalf at hh
    nlinarith
  obtain ⟨b₁, hb₁, b₂, hb₂, b₃, hb₃, hx2', p1, p2, p3, ps⟩ := alsetri_prop32 (F a₁) (F a₂) (F a₃)
    (fun v => hf _) (fun v => hf _) (fun v => hf _) (hFs a₁) (hFs a₂) (hFs a₃) hT (e x).2 hx2
  refine ⟨e.symm (a₁, b₁), ?_, e.symm (a₂, b₂), ?_, e.symm (a₃, b₃), ?_, ?_, p1, p2, p3, ps⟩
  · rw [mem_unitsMod_crt hc, RingEquiv.apply_symm_apply]; exact ⟨ha₁, hb₁⟩
  · rw [mem_unitsMod_crt hc, RingEquiv.apply_symm_apply]; exact ⟨ha₂, hb₂⟩
  · rw [mem_unitsMod_crt hc, RingEquiv.apply_symm_apply]; exact ⟨ha₃, hb₃⟩
  · apply e.injective
    rw [map_add, map_add, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply,
      RingEquiv.apply_symm_apply, Prod.mk_add_mk, Prod.mk_add_mk, ← hx1, ← hx2']

/-- **P0085 Theorem 1.2**, Alsetri's local result, for every odd squarefree `m` with `3 ∣ m`.
Same statement as `alsetri_1_2` in Alsetri2025.lean. -/
theorem alsetri12_proved (m : ℕ) [NeZero m] (hodd : Odd m) (hsq : Squarefree m) (h3 : 3 ∣ m) :
    Alsetri12 m := by
  by_cases h5 : 5 ∣ m
  · have h15 : 15 ∣ m := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3 h5
    obtain ⟨k, rfl⟩ := h15
    have hk : k ≠ 0 := fun h => NeZero.ne (15 * k) (by simp [h])
    have : NeZero k := ⟨hk⟩
    have : NeZero (k * 15) := ⟨by positivity⟩
    have hsq' : Squarefree k := hsq.of_mul_right
    have n3 : ¬ 3 ∣ k := by
      rintro ⟨t, rfl⟩
      have := hsq 3 ⟨5 * t, by ring⟩
      exact absurd (Nat.isUnit_iff.1 this) (by norm_num)
    have n5 : ¬ 5 ∣ k := by
      rintro ⟨t, rfl⟩
      have := hsq 5 ⟨3 * t, by ring⟩
      exact absurd (Nat.isUnit_iff.1 this) (by norm_num)
    have n2 : ¬ 2 ∣ k := by
      rintro ⟨t, rfl⟩
      obtain ⟨r, hr⟩ := hodd
      omega
    have c2 : Nat.Coprime 2 k := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 n2
    have c3 : Nat.Coprime 3 k := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 n3
    have c5 : Nat.Coprime 5 k := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 n5
    have c30 : Nat.Coprime k 30 :=
      (Nat.Coprime.mul_left (Nat.Coprime.mul_left c2 c3) c5).symm
    have c15 : Nat.Coprime k 15 := (Nat.Coprime.mul_left c3 c5).symm
    exact alsetri12_congr (mul_comm k 15)
      (alsetri12_of_half31_15 k c15 (half31_coprime30 k hsq' c30))
  · exact alsetri12_of_coprime5 m hodd hsq h3 h5

end LeanLab.DensityGoldbach

#print axioms LeanLab.DensityGoldbach.alsetri12_proved
