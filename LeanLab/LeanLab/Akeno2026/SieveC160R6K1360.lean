/-
P0087 Akeno 2026 Appendix 5.1 page 36.
Grid 1/160 certificates. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Akeno2026.SieveCTables160Data
namespace LeanLab.Akeno2026.SieveFns.Grid160
theorem chk_c6_1360 : ∀ k < 1440, 1360 ≤ k → checks6 k := by
  unfold checks6
  decide +kernel
end LeanLab.Akeno2026.SieveFns.Grid160
