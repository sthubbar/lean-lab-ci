import LeanLab.HeathBrownPuchta.Decomp1530Core215

/-! P0012 page 30 display 44. Existing private certificate checks moved verbatim. -/
namespace LeanLab.HeathBrownPuchta.Decomp1530c
open Finset Real LeanLab.HeathBrownPuchta.Decomp1530a LeanLab.HeathBrownPuchta.Decomp1530b
open LeanLab.Linnik
attribute [local instance 10] Classical.propDecidable
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open LeanLab.HeathBrownPuchta.Decomp1530c.CoreExports215

private lemma ckc0 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 0 + k.val) % 65536)
      (65536 - (512 * 0 + k.val) % 65536)) = rawI (512 * 0 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 0 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 0 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 0 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc1 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 1 + k.val) % 65536)
      (65536 - (512 * 1 + k.val) % 65536)) = rawI (512 * 1 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 1 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 1 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 1 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc2 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 2 + k.val) % 65536)
      (65536 - (512 * 2 + k.val) % 65536)) = rawI (512 * 2 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 2 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 2 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 2 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc3 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 3 + k.val) % 65536)
      (65536 - (512 * 3 + k.val) % 65536)) = rawI (512 * 3 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 3 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 3 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 3 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc4 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 4 + k.val) % 65536)
      (65536 - (512 * 4 + k.val) % 65536)) = rawI (512 * 4 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 4 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 4 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 4 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc5 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 5 + k.val) % 65536)
      (65536 - (512 * 5 + k.val) % 65536)) = rawI (512 * 5 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 5 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 5 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 5 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc6 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 6 + k.val) % 65536)
      (65536 - (512 * 6 + k.val) % 65536)) = rawI (512 * 6 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 6 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 6 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 6 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc7 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 7 + k.val) % 65536)
      (65536 - (512 * 7 + k.val) % 65536)) = rawI (512 * 7 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 7 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 7 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 7 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc8 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 8 + k.val) % 65536)
      (65536 - (512 * 8 + k.val) % 65536)) = rawI (512 * 8 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 8 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 8 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 8 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc9 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 9 + k.val) % 65536)
      (65536 - (512 * 9 + k.val) % 65536)) = rawI (512 * 9 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 9 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 9 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 9 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc10 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 10 + k.val) % 65536)
      (65536 - (512 * 10 + k.val) % 65536)) = rawI (512 * 10 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 10 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 10 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 10 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc11 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 11 + k.val) % 65536)
      (65536 - (512 * 11 + k.val) % 65536)) = rawI (512 * 11 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 11 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 11 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 11 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc12 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 12 + k.val) % 65536)
      (65536 - (512 * 12 + k.val) % 65536)) = rawI (512 * 12 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 12 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 12 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 12 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc13 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 13 + k.val) % 65536)
      (65536 - (512 * 13 + k.val) % 65536)) = rawI (512 * 13 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 13 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 13 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 13 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc14 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 14 + k.val) % 65536)
      (65536 - (512 * 14 + k.val) % 65536)) = rawI (512 * 14 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 14 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 14 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 14 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc15 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 15 + k.val) % 65536)
      (65536 - (512 * 15 + k.val) % 65536)) = rawI (512 * 15 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 15 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 15 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 15 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc16 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 16 + k.val) % 65536)
      (65536 - (512 * 16 + k.val) % 65536)) = rawI (512 * 16 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 16 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 16 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 16 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc17 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 17 + k.val) % 65536)
      (65536 - (512 * 17 + k.val) % 65536)) = rawI (512 * 17 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 17 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 17 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 17 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc18 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 18 + k.val) % 65536)
      (65536 - (512 * 18 + k.val) % 65536)) = rawI (512 * 18 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 18 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 18 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 18 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc19 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 19 + k.val) % 65536)
      (65536 - (512 * 19 + k.val) % 65536)) = rawI (512 * 19 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 19 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 19 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 19 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc20 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 20 + k.val) % 65536)
      (65536 - (512 * 20 + k.val) % 65536)) = rawI (512 * 20 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 20 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 20 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 20 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc21 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 21 + k.val) % 65536)
      (65536 - (512 * 21 + k.val) % 65536)) = rawI (512 * 21 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 21 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 21 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 21 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc22 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 22 + k.val) % 65536)
      (65536 - (512 * 22 + k.val) % 65536)) = rawI (512 * 22 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 22 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 22 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 22 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc23 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 23 + k.val) % 65536)
      (65536 - (512 * 23 + k.val) % 65536)) = rawI (512 * 23 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 23 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 23 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 23 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc24 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 24 + k.val) % 65536)
      (65536 - (512 * 24 + k.val) % 65536)) = rawI (512 * 24 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 24 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 24 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 24 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc25 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 25 + k.val) % 65536)
      (65536 - (512 * 25 + k.val) % 65536)) = rawI (512 * 25 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 25 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 25 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 25 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc26 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 26 + k.val) % 65536)
      (65536 - (512 * 26 + k.val) % 65536)) = rawI (512 * 26 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 26 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 26 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 26 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc27 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 27 + k.val) % 65536)
      (65536 - (512 * 27 + k.val) % 65536)) = rawI (512 * 27 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 27 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 27 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 27 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc28 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 28 + k.val) % 65536)
      (65536 - (512 * 28 + k.val) % 65536)) = rawI (512 * 28 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 28 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 28 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 28 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc29 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 29 + k.val) % 65536)
      (65536 - (512 * 29 + k.val) % 65536)) = rawI (512 * 29 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 29 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 29 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 29 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc30 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 30 + k.val) % 65536)
      (65536 - (512 * 30 + k.val) % 65536)) = rawI (512 * 30 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 30 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 30 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 30 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc31 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 31 + k.val) % 65536)
      (65536 - (512 * 31 + k.val) % 65536)) = rawI (512 * 31 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 31 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 31 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 31 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs


namespace CosA215Exports
export LeanLab.HeathBrownPuchta.Decomp1530c (ckc0 ckc1 ckc2 ckc3 ckc4 ckc5 ckc6 ckc7 ckc8 ckc9 ckc10 ckc11 ckc12 ckc13 ckc14 ckc15 ckc16 ckc17 ckc18 ckc19 ckc20 ckc21 ckc22 ckc23 ckc24 ckc25 ckc26 ckc27 ckc28 ckc29 ckc30 ckc31)
end CosA215Exports

end LeanLab.HeathBrownPuchta.Decomp1530c
