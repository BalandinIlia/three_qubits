import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Subalgebra
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Submodule.Bilinear

-- A pair
@[ext]
structure Coup(R:Type)[r: Ring R] where
f: R
s: R

@[instance]
instance mon(R:Type)[r: Ring R]: AddCommMonoid (Coup R) :=
{
  add(c1 c2: (Coup R)):(Coup R) := Coup.mk (c1.f+c2.f) (c1.s+c2.s)
  zero := Coup.mk 0 0
  add_assoc := by
    intros
    ext
    all_goals apply r.add_assoc
  zero_add := by
    intros
    ext
    all_goals apply r.zero_add
  add_zero := by
    intros
    ext
    all_goals apply r.add_zero
  add_comm := by
    intros
    ext
    all_goals apply r.add_comm

  nsmul(n: ℕ)(c:Coup R) := Coup.mk (n*c.f) (n*c.s)
  nsmul_zero := by
    intro x
    simp [OfNat.ofNat]
    apply And.intro
    all_goals apply r.zero_mul
  nsmul_succ := by
    intro n x
    ext
    all_goals simp [HAdd.hAdd]
    all_goals simp [Add.add]
    all_goals rw [r.right_distrib]
    all_goals simp
    all_goals simp [HAdd.hAdd]
}
/-
@[instance]
instance g(R: Type)[r: Ring R]: HSMul R (Coup R) (Coup R) :=
{
  hSMul(z:R)(c:Coup R):Coup R := Coup.mk (z*c.f) (z*c.s)
}

@[instance]
instance gg(R: Type)[r: Ring R]: HMul R (Coup R) (Coup R) :=
{
  hMul(z:R)(c:Coup R):Coup R := Coup.mk (z*c.f) (z*c.s)
}
-/
@[instance]
instance mod(R: Type)[r: Ring R]: Module R (Coup R) :=
{
  smul(z:R)(c: Coup R) := Coup.mk (z*c.f) (z*c.s)
  one_smul := by simp [HSMul.hSMul]
  mul_smul := by
    simp [HSMul.hSMul]
    intro x y b
    apply And.intro
    all_goals apply r.mul_assoc
  smul_zero := by
    simp [HSMul.hSMul]
    intro a
    ext
    all_goals simp [OfNat.ofNat]
    all_goals simp [Zero.zero]
  smul_add := by
    simp [HSMul.hSMul, HAdd.hAdd]
    intro a x y
    simp [Add.add]
    apply And.intro
    all_goals apply r.left_distrib
  add_smul := by
    intro a b
    intro x
    simp [HSMul.hSMul, HAdd.hAdd]
    simp [Add.add]
    apply And.intro
    all_goals apply r.right_distrib
  zero_smul := by
    simp [HSMul.hSMul]
    ext
    all_goals simp [OfNat.ofNat]
    all_goals simp [Zero.zero]
    all_goals aesop
}
