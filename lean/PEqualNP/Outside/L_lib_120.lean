import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_120 : ∀ (t : ℕ → ℕ) (L : Language Bool), L ∈ PEqualNP.Library.DTIME t → Lᶜ ∈ PEqualNP.Library.DTIME t := by
  intro t L hL
  obtain ⟨f, hf, c, hc⟩ := hL
  refine ⟨fun a => !f a, ?_, ?_⟩
  · intro a
    have := hf a
    change a ∉ L ↔ (!f a) = true
    rw [Bool.not_eq_true', ← Bool.not_eq_true, ← this]; rfl
  · refine ⟨⟨⟨c.tm, c.inputAlphabet, c.outputAlphabet.trans Equiv.boolNot⟩, c.time, ?_⟩, hc⟩
    intro a
    have h := c.outputsFun a
    convert h using 2
    cases f a <;> rfl
