import Colean.MutualCmd

/-! # Test: regressions

Declarations that once failed, kept as checks of the fixes. -/

namespace RegressionTest

noncomputable section

/-! ### A nested argument at the constructor's own index, another at a fixed one

`T.Colean.rel_ofC` named the premises of `T.F.Rel.c1` by their positions after `cases`, but the
substitution of the index variable puts the hypotheses that depend on it (those of `x1`) after the
others (those of `x2`), so the names went to the wrong premises. -/

codatatype Q : Nat → Type
  | c1 {n : Nat} (x1 : Option (Q n)) (x2 : Q 0) : Q n
  | c2 : Q 0

#check @Q.c1
#check @Q.corec
#check @Q.bisim
#check @Q.Colean.rel_ofC

def Q.zeros : Q 0 := Q.corec (S := fun _ => Unit) (fun _ _ => .c1 none ()) ()

example : Q.zeros.dtor = .c1 none Q.zeros := by
  simp [Q.zeros]

example (q : Q 0) : True := by
  cases q with
  | c1 x1 x2 => trivial
  | c2 => trivial

-- Only `c1` is at a successor.
example {n : Nat} (q : Q (n + 1)) : True := by
  cases q with
  | c1 x1 x2 => trivial

-- Variants that worked before the fix.
codatatype QPlain : Nat → Type
  | c1 {n : Nat} (x1 : QPlain n) (x2 : QPlain 0) : QPlain n
  | c2 : QPlain 0

codatatype QOne : Nat → Type
  | c1 {n : Nat} (x1 : Option (QOne n)) : QOne n
  | c2 : QOne 0

codatatype QZero : Nat → Type
  | c1 {n : Nat} (x1 : Option (QZero 0)) (x2 : QZero 0) : QZero n
  | c2 : QZero 0

codatatype QSecond : Nat → Type
  | c1 {n : Nat} (x2 : QSecond 0) (x1 : Option (QSecond n)) : QSecond n
  | c2 : QSecond 0

datatype D : Nat → Type
  | c1 {n : Nat} (x1 : Option (D n)) (x2 : D 0) : D n
  | c2 : D 0

-- Variants that failed as `Q` did.
codatatype QList : Nat → Type
  | c1 {n : Nat} (x1 : List (QList n)) (x2 : QList 0) : QList n
  | c2 : QList 0

codatatype QTwo : Nat → Type
  | c1 {n : Nat} (x1 : Option (QTwo n)) (x2 : List (QTwo 0)) : QTwo n
  | c2 : QTwo 0

codatatype QThree : Nat → Type
  | c1 {n : Nat} (x1 : Option (QThree n)) (x2 : List (QThree 0)) (x3 : QThree (n + 1)) :
      QThree n
  | c2 : QThree 0

codatatype QAround : Nat → Type
  | c1 {n : Nat} (x0 : QAround 0) (x1 : Option (QAround n)) (x2 : QAround 0) : QAround n
  | c2 : QAround 0

example (q : QThree 0) : True := by
  cases q with
  | c1 x1 x2 x3 => trivial
  | c2 => trivial

-- The same shape in a block, which worked before the fix.
mutual
codatatype M1 : Nat → Type
  | c1 {n : Nat} (x1 : Option (M1 n)) (x2 : M2 0) : M1 n
  | c2 : M1 0
codatatype M2 : Nat → Type
  | d1 {n : Nat} (y1 : List (M2 n)) (y2 : M1 0) : M2 n
  | d2 : M2 0
end

#check @M1.bisim

end

end RegressionTest
