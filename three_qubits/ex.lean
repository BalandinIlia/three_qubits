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
import three_qubits.one_qubit
import three_qubits.reg
import three_qubits.CF_rise
import three_qubits.insert
import three_qubits.CF2

#check TensorProduct.add_smul
#check TensorProduct.add_tmul
#check TensorProduct.tmul_add
#check TensorProduct.smul_tmul
#check TensorProduct.smul_tmul'
noncomputable
def swappp:CF2 ℤ :=
{
  func := fun x y:Coup ℤ  => pureDoub ℤ y x
  ps1:= by
    simp [pureDoub]
    intro a b c
    rw [TensorProduct.tmul_add c a b]
  ps2:= by
    simp [pureDoub]
    intro a b c
    rw [TensorProduct.add_tmul]
  pm1:= by
    simp [pureDoub]
  pm2:= by
    simp [pureDoub]
    intro m a b
    rw [TensorProduct.smul_tmul']
}

noncomputable
def swa(p1 p2:ℕ)(neq: ¬(p1=p2)):=transTwo ℤ swappp p1 p2 neq

def swap1:Coup ℤ →ₗ[ℤ] Coup ℤ :=
{
  toFun(x: Coup ℤ) := Coup.mk x.s x.f
  map_add' := by
    sorry
  map_smul' := by
    sorry
}

noncomputable
def core(n: ℕ)
        (tr: Coup ℤ →ₗ[ℤ] Coup ℤ)
        (x: Coup ℤ)
        (y: Coup ℤ)
        (z: Coup ℤ):
        triple ℤ :=
if (n=1) then TensorProduct.tmul ℤ
                                 (TensorProduct.tmul ℤ (tr x) y)
                                 z
else if (n=2) then TensorProduct.tmul ℤ
                                      (TensorProduct.tmul ℤ x (tr y))
                                      z
else if (n=3) then TensorProduct.tmul ℤ
                                      (TensorProduct.tmul ℤ x y)
                                      (tr z)
else TensorProduct.tmul ℤ
                        (TensorProduct.tmul ℤ x y)
                        z

noncomputable
def coreFunc(n: ℕ)(tr: Coup ℤ →ₗ[ℤ] Coup ℤ): CF ℤ :=
{
  func := core n tr
  ps1 := by
    simp [core]
    intros
    unfoldTensorPrSum
    apply help n
    all_goals aesop
  ps2 := by
    simp [core]
    intros
    unfoldTensorPrSum
    apply help n
    all_goals aesop
  ps3 := by
    simp [core]
    intros
    unfoldTensorPrSum
    apply help n
    all_goals aesop
  pm1 := by
    simp [core]
    intros
    apply help n
    all_goals aesop
  pm2 := by
    simp [core]
    intros
    apply help n
    all_goals aesop
  pm3 := by
    simp [core]
}

-- triple examples
noncomputable
def ex1:triple ℤ := TensorProduct.tmul ℤ (TensorProduct.tmul ℤ (Coup.mk 1 2) (Coup.mk 3 4)) (Coup.mk 5 6)
noncomputable
def ex2:triple ℤ := TensorProduct.tmul ℤ (TensorProduct.tmul ℤ (Coup.mk 10 20) (Coup.mk 30 40)) (Coup.mk 50 60)

--Part 4: tests

-- first test theorem to make sure that final works as expected
theorem test1:final ℤ (coreFunc 1 swap1) ex1 = TensorProduct.tmul ℤ (TensorProduct.tmul ℤ (Coup.mk 2 1) (Coup.mk 3 4)) (Coup.mk 5 6) := by
  simp [ex1]
  simp [final]
  simp [coreLift1]
  simp [coreLin3, coreLin2, coreLin1]
  simp [coreFunc]
  simp [swap1]
  simp [core]

theorem testt:final ℤ (swa 1 3 (by aesop)) ex1 = TensorProduct.tmul ℤ (TensorProduct.tmul ℤ (Coup.mk 5 6) (Coup.mk 3 4)) (Coup.mk 1 2) := by
  simp [ex1]
  simp [final]
  simp [coreLift1]
  simp [coreLin3, coreLin2, coreLin1]
  simp [swa, swappp, transTwo, repl, repl2, sel, pureDoub, repl1, pureTriple]

theorem testtt:final ℤ (swa 1 3 (by aesop)) (ex1+ex2) = TensorProduct.tmul ℤ (TensorProduct.tmul ℤ (Coup.mk 5 6) (Coup.mk 3 4)) (Coup.mk 1 2)
      + TensorProduct.tmul ℤ (TensorProduct.tmul ℤ (Coup.mk 50 60) (Coup.mk 30 40)) (Coup.mk 10 20)
  := by
  simp [ex1, ex2]
  simp [final]
  simp [coreLift1]
  simp [coreLin3, coreLin2, coreLin1]
  simp [swa, swappp, transTwo, repl, repl2, sel, pureDoub, repl1, pureTriple]

theorem test2:final ℤ (coreFunc 2 swap1) ex1 = TensorProduct.tmul ℤ (TensorProduct.tmul ℤ (Coup.mk 1 2) (Coup.mk 4 3)) (Coup.mk 5 6) := by
  simp [ex1]
  simp [final]
  simp [coreLift1]
  simp [coreLin3, coreLin2, coreLin1]
  simp [coreFunc]
  simp [swap1]
  simp [core]

theorem test3:final ℤ (coreFunc 2 swap1) (ex1+ex2) =
            TensorProduct.tmul ℤ (TensorProduct.tmul ℤ (Coup.mk 1 2) (Coup.mk 4 3)) (Coup.mk 5 6) +
            TensorProduct.tmul ℤ (TensorProduct.tmul ℤ (Coup.mk 10 20) (Coup.mk 40 30)) (Coup.mk 50 60) := by
  have eq: final ℤ (coreFunc 2 swap1) (ex1+ex2) = (final ℤ (coreFunc 2 swap1) ex1) + (final ℤ (coreFunc 2 swap1) ex2) := by
    simp [final]
  rw [eq]
  clear eq

  simp [ex1, ex2]
  simp [final]
  simp [coreLift1]
  simp [coreLin3, coreLin2, coreLin1]
  simp [coreFunc]
  simp [swap1]
  simp [core]


theorem test4:final ℤ (coreFunc 3 swap1) ex1 = TensorProduct.tmul ℤ (TensorProduct.tmul ℤ (Coup.mk 1 2) (Coup.mk 3 4)) (Coup.mk 6 5) := by
  simp [ex1]
  simp [final]
  simp [coreLift1]
  simp [coreLin3, coreLin2, coreLin1]
  simp [coreFunc]
  simp [swap1]
  simp [core]
