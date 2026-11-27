import Theorems.EuclidLemma.A
import Theorems.EuclidLemma.B

namespace TuriMath.EuclidLemma

/-- Statements A and B correspond: unfold both and match hypotheses and conclusions. -/
theorem equiv : A.Statement ↔ B.Statement := by
  constructor
  · intro h p a b hp hd
    have hp' : Nat.Prime p := Nat.prime_def.mpr hp
    have hd' : (p : ℤ) ∣ a * b := hd
    exact h p hp' a b hd'
  · intro h p hp a b hd
    have hp' : B.IsPrimeB p := Nat.prime_def.mp hp
    exact h p a b hp' hd

end TuriMath.EuclidLemma
